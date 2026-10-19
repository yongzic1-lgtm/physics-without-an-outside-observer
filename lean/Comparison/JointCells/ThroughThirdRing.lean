import Comparison.Elements.TwoThings

/-!
# Comparisons compose through a third (Proposition 90)

When three systems are compared with each other, the order of the
comparisons does not change the result, and this is not a postulate but a result of the geometry: its only inputs are
the composition of P1 (operators on different systems commute) and Proposition 4 (from P3: the five directions of one system
anticommute in pairs and square to one). The original keeps it as Proposition 90:

    L_ab(A) = 1 + Σ_{s,t} A_st γ_s^(a) γ_t^(b),     ½{L_ab(A), L_ac(B)} = L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2.

Comparing `a` with `b` in the frame `A` and `a` with `c` in the frame `B`, taken in either order, compares `b` with `c`
in the frame `AᵀB`, with weight one.

* `through_third_core`: the identity for any ring in which the lines of `a` anticommute (`γ_sγ_u + γ_uγ_s = 2δ_su`,
  Proposition 4) and operators on different systems commute (P1's composition): these two hypotheses are all it uses,
  and no orthogonality of the frames; the part of `L_ab L_ac` that depends on the order is the commutator, the rotation.
* `through_third`: Proposition 90 itself, with the one.
* `three_lines_*`, `prop90_model`: the same for the model of Proposition 23 on three systems, `ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁴`, with the
  five directions `γ` of `Elements/OneThing.lean`.
* For the two-spinor states of two systems, whose frame is the meeting's division `θ_U` (Proposition 129): `xor_frames`, the
  third two-spinor state is `U △ V` (Proposition 25's composition is Proposition 90 on these frames); `flat_triangle`, around the
  three two-spinor states of three systems the frames multiply to one, so on every line the three agreement signs multiply to
  `+1`; `flat_triangle_orth`, the same around any three frames `A`, `AᵀB`, `Bᵀ`.
* `plane_colour_through_third`: the plane `F` and its colour counterpart `C` are joined through a third, `θ_Fᵀ θ_{all} = θ_C`, by
  the frame `−1` of the singlet's counterpart `{n}`; `join_needs_improper`: every frame `B` with `θ_Fᵀ B = θ_C` has `det B = −1`;
  `relations_stay_even`: two two-spinor states compose to a two-spinor state, never to the odd `C`.
-/

open Matrix Kronecker Finset

namespace Comparison.JointCells

/-! ## The identity in any ring -/

section Abstract

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The comparison part `Σ_{s,t} A_st x_s y_t` of two systems in the frame `A`. -/
def cmpPart (A : Matrix (Fin 5) (Fin 5) ℂ) (x y : Fin 5 → R) : R :=
  ∑ s, ∑ t, A s t • (x s * y t)

/-- The comparison `L(A) = 1 + Σ A_st x_s y_t` (Definition 10 with a frame). -/
def compL (A : Matrix (Fin 5) (Fin 5) ℂ) (x y : Fin 5 → R) : R := 1 + cmpPart A x y

/-- `Σ_t A_st y_t`: the lines of the second system seen along the line `s` of the first in the frame `A`. -/
def along (A : Matrix (Fin 5) (Fin 5) ℂ) (y : Fin 5 → R) (s : Fin 5) : R := ∑ t, A s t • y t

theorem cmpPart_eq (A : Matrix (Fin 5) (Fin 5) ℂ) (x y : Fin 5 → R) :
    cmpPart A x y = ∑ s, x s * along A y s := by
  unfold cmpPart along
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm]

theorem along_comm {x y : Fin 5 → R} (hxy : ∀ s t, x s * y t = y t * x s)
    (A : Matrix (Fin 5) (Fin 5) ℂ) (s u : Fin 5) : x u * along A y s = along A y s * x u := by
  unfold along
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hxy]

theorem along_along_comm {y z : Fin 5 → R} (hyz : ∀ t v, y t * z v = z v * y t)
    (A B : Matrix (Fin 5) (Fin 5) ℂ) (s u : Fin 5) :
    along A y s * along B z u = along B z u * along A y s := by
  unfold along
  calc (∑ t, A s t • y t) * (∑ v, B u v • z v) = ∑ t, ∑ v, (A s t • y t) * (B u v • z v) := by
        rw [Finset.sum_mul_sum]
    _ = ∑ t, ∑ v, (B u v • z v) * (A s t • y t) := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => ?_
        rw [smul_mul_smul_comm, smul_mul_smul_comm, hyz, mul_comm (A s t)]
    _ = ∑ v, ∑ t, (B u v • z v) * (A s t • y t) := Finset.sum_comm
    _ = (∑ v, B u v • z v) * (∑ t, A s t • y t) := by rw [Finset.sum_mul_sum]

theorem sum_along_along (A B : Matrix (Fin 5) (Fin 5) ℂ) (y z : Fin 5 → R) :
    ∑ s, along A y s * along B z s = cmpPart (Aᵀ * B) y z := by
  unfold along cmpPart
  calc ∑ s, (∑ t, A s t • y t) * (∑ v, B s v • z v)
      = ∑ s, ∑ t, ∑ v, (A s t * B s v) • (y t * z v) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => ?_
        rw [smul_mul_smul_comm]
    _ = ∑ t, ∑ s, ∑ v, (A s t * B s v) • (y t * z v) := Finset.sum_comm
    _ = ∑ t, ∑ v, ∑ s, (A s t * B s v) • (y t * z v) := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ t, ∑ v, (Aᵀ * B) t v • (y t * z v) := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => ?_
        rw [Matrix.mul_apply, Finset.sum_smul]
        rfl

omit [Algebra ℂ R] in
theorem swap_left (a b c : R) (h : b * a = a * b) : b * (a * c) = a * (b * c) := by
  rw [← mul_assoc, h, mul_assoc]

/-- **Comparisons compose through a third, the core:** `XY + YX = 2 Σ_{t,v} (AᵀB)_tv y_t z_v` for
`X = Σ A_st x_s y_t`, `Y = Σ B_uv x_u z_v`. -/
theorem through_third_core (A B : Matrix (Fin 5) (Fin 5) ℂ) (x y z : Fin 5 → R)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : ℂ) else 0) • (1 : R))
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) :
    cmpPart A x y * cmpPart B x z + cmpPart B x z * cmpPart A x y =
      (2 : ℂ) • cmpPart (Aᵀ * B) y z := by
  rw [cmpPart_eq A x y, cmpPart_eq B x z, ← sum_along_along A B y z]
  have e1 : (∑ s, x s * along A y s) * (∑ u, x u * along B z u) =
      ∑ s, ∑ u, x s * x u * (along A y s * along B z u) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [mul_assoc]
    rw [swap_left _ _ _ (along_comm hxy A s u).symm]
  have e2 : (∑ u, x u * along B z u) * (∑ s, x s * along A y s) =
      ∑ s, ∑ u, x u * x s * (along A y s * along B z u) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [mul_assoc]
    rw [swap_left _ _ _ (along_comm hxz B u s).symm, (along_along_comm hyz A B s u).symm]
  rw [e1, e2, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  have e3 : ∀ u, x s * x u * (along A y s * along B z u) + x u * x s * (along A y s * along B z u) =
      (if s = u then (2 : ℂ) else 0) • (along A y s * along B z u) := by
    intro u
    rw [← add_mul, hx s u, smul_mul_assoc, one_mul]
  rw [Finset.sum_congr rfl fun u _ => e3 u]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Proposition 90, comparisons compose through a third:**
`L_ab(A) L_ac(B) + L_ac(B) L_ab(A) = 2 (L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2)`, the order of the two comparisons free,
the comparison of `b` with `c` in the frame `AᵀB` entering with weight one. -/
theorem through_third (A B : Matrix (Fin 5) (Fin 5) ℂ) (x y z : Fin 5 → R)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : ℂ) else 0) • (1 : R))
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) :
    compL A x y * compL B x z + compL B x z * compL A x y =
      (2 : ℂ) • (compL A x y + compL B x z + compL (Aᵀ * B) y z - (2 : ℂ) • 1) := by
  have h := through_third_core A B x y z hx hxy hxz hyz
  unfold compL
  have expand : (1 + cmpPart A x y) * (1 + cmpPart B x z) + (1 + cmpPart B x z) * (1 + cmpPart A x y) =
      (1 + cmpPart A x y + cmpPart B x z) + (1 + cmpPart A x y + cmpPart B x z) +
        (cmpPart A x y * cmpPart B x z + cmpPart B x z * cmpPart A x y) := by
    noncomm_ring
  rw [expand, h]
  simp only [two_smul]
  abel

end Abstract

/-! ## The model of Proposition 23 on three systems -/

section Model

open Comparison

/-- Three systems: `ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁴`. -/
abbrev Three := (Four × Four) × Four

/-- The line `s` on the first system. -/
noncomputable def γa (s : Fin 5) : Matrix Three Three ℂ :=
  (γ s ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ (1 : Matrix Four Four ℂ)

/-- The line `t` on the second system. -/
noncomputable def γb (t : Fin 5) : Matrix Three Three ℂ :=
  ((1 : Matrix Four Four ℂ) ⊗ₖ γ t) ⊗ₖ (1 : Matrix Four Four ℂ)

/-- The line `v` on the third system. -/
noncomputable def γc (v : Fin 5) : Matrix Three Three ℂ :=
  ((1 : Matrix Four Four ℂ) ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ γ v

theorem three_lines_clifford (s u : Fin 5) :
    γa s * γa u + γa u * γa s = (if s = u then (2 : ℂ) else 0) • (1 : Matrix Three Three ℂ) := by
  simp only [γa, ← mul_kronecker_mul, Matrix.mul_one]
  rw [← add_kronecker, ← add_kronecker, clifford, smul_kronecker, smul_kronecker, one_kronecker_one,
    one_kronecker_one]

theorem three_ab (s t : Fin 5) : γa s * γb t = γb t * γa s := by
  simp only [γa, γb, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem three_ac (s v : Fin 5) : γa s * γc v = γc v * γa s := by
  simp only [γa, γc, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem three_bc (t v : Fin 5) : γb t * γc v = γc v * γb t := by
  simp only [γb, γc, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- **Proposition 90 in the model, on three systems:** comparing the first system with the second in the frame `A` and
with the third in the frame `B`, in either order, compares the second with the third in the frame `AᵀB`. -/
theorem prop90_model (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    compL A γa γb * compL B γa γc + compL B γa γc * compL A γa γb =
      (2 : ℂ) • (compL A γa γb + compL B γa γc + compL (Aᵀ * B) γb γc - (2 : ℂ) • 1) :=
  through_third A B γa γb γc three_lines_clifford three_ab three_ac three_bc

end Model

/-! ## On the two-spinor states: the third two-spinor state, the flat triangle, and the plane joined to its colour counterpart -/

section Frames

/-- The frame of a two-spinor state `e_U`, the meeting's division on the five directions (Proposition 129):
`θ_U = diag((−1)^{[t ∈ U]})`; for an odd `U` it is the counterpart's (Definition 37). -/
noncomputable def frame (U : Finset (Fin 5)) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal fun t => if t ∈ U then -1 else 1

theorem frame_transpose (U : Finset (Fin 5)) : (frame U)ᵀ = frame U := diagonal_transpose _

/-- **Through a third, two two-spinor states make the third:** `θ_Uᵀ θ_V = θ_{U △ V}`; Proposition 25's composition of the
two-spinor states of three systems is Proposition 90 on the meetings' frames. -/
theorem xor_frames (U V : Finset (Fin 5)) : (frame U)ᵀ * frame V = frame (symmDiff U V) := by
  rw [frame_transpose, frame, frame, frame, diagonal_mul_diagonal]
  congr 1
  funext t
  by_cases hU : t ∈ U <;> by_cases hV : t ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- **The flat triangle:** around the three two-spinor states of three systems the frames multiply to one,
`θ_U θ_{U△V} θ_V = 1`: on every line the three agreement signs multiply to `+1`. -/
theorem flat_triangle (U V : Finset (Fin 5)) : frame U * frame (symmDiff U V) * frame V = 1 := by
  rw [frame, frame, frame, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext t
  by_cases hU : t ∈ U <;> by_cases hV : t ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- **No triangle of two-spinor states returns `−1`:** the sign of the three agreements on a line is `+1` at every record. -/
theorem triangle_sign_one (U V : Finset (Fin 5)) (r : Fin 5) :
    (if r ∈ U then (-1 : ℂ) else 1) * (if r ∈ symmDiff U V then -1 else 1) * (if r ∈ V then -1 else 1) = 1 := by
  by_cases hU : r ∈ U <;> by_cases hV : r ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- The same around any three frames composed through a third: `A (AᵀB) Bᵀ = 1` for orthogonal `A, B`. -/
theorem flat_triangle_orth (A B : Matrix (Fin 5) (Fin 5) ℂ) (hA : A * Aᵀ = 1) (hB : B * Bᵀ = 1) :
    A * (Aᵀ * B) * Bᵀ = 1 := by
  rw [← Matrix.mul_assoc, hA, Matrix.one_mul, hB]

/-- Two pairs of three systems at the plane meeting put the third pair at the singlet. -/
theorem plane_plane_singlet : symmDiff ({0, 1} : Finset (Fin 5)) {0, 1} = ∅ := by
  decide

/-- The frame of all five lines reversed, the singlet's counterpart `{n}`, is `−1`. -/
theorem frame_univ : frame Finset.univ = -1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [frame]
  · simp [frame, h]

/-- **The plane and its colour counterpart are joined through a third:** `θ_Fᵀ θ_{all five} = θ_C` with `F = {h, k}`,
`C = {c₁, c₂, c₃}`, the third compared in the frame `−1` of the singlet's counterpart `{n}`. -/
theorem plane_colour_through_third :
    (frame ({0, 1} : Finset (Fin 5)))ᵀ * frame Finset.univ = frame ({2, 3, 4} : Finset (Fin 5)) := by
  rw [xor_frames]
  congr 1

theorem frame_det_plane : (frame ({0, 1} : Finset (Fin 5))).det = 1 := by
  simp [frame, det_diagonal, Fin.prod_univ_five]

theorem frame_det_colour : (frame ({2, 3, 4} : Finset (Fin 5))).det = -1 := by
  simp [frame, det_diagonal, Fin.prod_univ_five]

/-- **Only an improper comparison joins them:** every frame `B` with `θ_Fᵀ B = θ_C` has `det B = −1`; turns
(determinant one) alone never join the plane to its colour counterpart. -/
theorem join_needs_improper (B : Matrix (Fin 5) (Fin 5) ℂ)
    (h : (frame ({0, 1} : Finset (Fin 5)))ᵀ * B = frame ({2, 3, 4} : Finset (Fin 5))) : B.det = -1 := by
  have h1 := congrArg Matrix.det h
  rw [det_mul, det_transpose, frame_det_plane, frame_det_colour, one_mul] at h1
  exact h1

/-- **Two-spinor states stay two-spinor states:** two even sets compose to an even set, so two two-spinor states never compose to the odd
colour counterpart. -/
theorem relations_stay_even : ∀ U V : Finset (Fin 5), Even U.card → Even V.card → Even (symmDiff U V).card := by
  decide

end Frames

end Comparison.JointCells

#print axioms Comparison.JointCells.through_third_core
#print axioms Comparison.JointCells.through_third
#print axioms Comparison.JointCells.three_lines_clifford
#print axioms Comparison.JointCells.prop90_model
#print axioms Comparison.JointCells.xor_frames
#print axioms Comparison.JointCells.flat_triangle
#print axioms Comparison.JointCells.triangle_sign_one
#print axioms Comparison.JointCells.flat_triangle_orth
#print axioms Comparison.JointCells.plane_plane_singlet
#print axioms Comparison.JointCells.frame_univ
#print axioms Comparison.JointCells.plane_colour_through_third
#print axioms Comparison.JointCells.join_needs_improper
#print axioms Comparison.JointCells.relations_stay_even
