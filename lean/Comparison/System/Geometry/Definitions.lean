import Comparison.System.Postulates
import Comparison.Elements.Turns
import Comparison.Article.Geometry2
import Comparison.GroupsContinuumLaw.Spin6
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# The geometry of comparison: the definitions (Definitions 1 to 16)

The definitions of Section III, each as a Lean object: the existing objects of the project under their canonical names
(`System/Basic.lean`), and the new ones the propositions need.

* **Definition 1** (system): a type `H` with `NormedAddCommGroup H`, `InnerProductSpace ℂ H`,
  `FiniteDimensional ℂ H` (P1).
* **Definition 2** (state): `P1.IsState` (a unit vector), `SameState` (equal up to a phase),
  `P1.IsMixedState`; an observable is a self-adjoint operator.
* **Definition 3** (quaternionic structure): `Partner.Θ`; its matrix in **every** orthonormal basis, `partnerMatrix`;
  the conjugate of an operator of the model, `partnerOp X = J Xᵀ J†`.
* **Definition 4** (distinction): `distinctionsH T`, the real space `Q` of the distinctions of every
  `(H, Θ)`; the normalized trace `τH`; the model's `IsDistinction`, `τ`.
* **Definition 5** (line): `gamma n = Σ n_s γ_s`, its sides `side n = (1 + γ(n))/2`, the ordered
  products `gammaS S = γ_{s₁}⋯γ_{s_r}`.
* **Definition 6** (plane): the operator `γ_sγ_t`.
* **Definition 7** (rotation): `SU4`, the generators `su4` (fifteen) and `sp2` (ten).
* **Definitions 8 to 11** (two-spinor state, the singlet, comparison, agreement): `relOf`, `relMat`, `swap`, `Ω`,
  `Eop`, `L`, `count`, `Ncount`, `disagreement`.
* **Definition 12** (the six directions): `sixDirections` (the antisymmetric two-spinor states), the Pfaffian
  `pfRel v = Pf M_v / Pf M_Ω`, `P1six` (`p(v) = ‖v‖²`), `P3six` (`(Θ ⊗ Θ)v = v`).
* **Definition 13** (division): a division of P1's real six is a subspace `D` of `E6`; its sign
  `Division.sign D` (`+1` on `Dᗮ`, `−1` on `D`), `Division.kind`, `Division.HoldsSinglet`; in a basis, a
  set `D ⊆ Fin 6` with the sign `theta R D`.
* **Definition 14** (half): `halfOf P = 1 − P + iP` for the projector `P` onto the divided part.
* **Definition 15** (metric, kept and moved, balanced, real form): `metricOf`, `KeptBy`, `MovedBy`,
  `Balanced`, `realFormAlg`, `realForm`.
* **Definition 16** (the sixty-four sets): `fS S`, the exterior products of the basis `f_a` of the six.
-/

open scoped InnerProductSpace Quaternion Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## Definitions 2 and 3: states and the quaternionic structure in every basis -/

/-- **Definition 2:** two unit vectors are the same state when they differ by a phase. -/
def SameState {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v w : H) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ w = c • v

section Partner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The quaternionic structure as an additive map. -/
def partnerAdd (T : Partner H) : H →+ H where
  toFun := T.Θ
  map_zero' := by
    have h : T.Θ 0 + T.Θ 0 = T.Θ 0 + 0 := by rw [add_zero, ← T.map_add, add_zero]
    exact add_left_cancel h
  map_add' := T.map_add

theorem partner_zero (T : Partner H) : T.Θ 0 = 0 := (partnerAdd T).map_zero

theorem partner_sum (T : Partner H) {ι : Type*} (s : Finset ι) (f : ι → H) :
    T.Θ (∑ i ∈ s, f i) = ∑ i ∈ s, T.Θ (f i) := map_sum (partnerAdd T) f s

theorem partner_neg (T : Partner H) (v : H) : T.Θ (-v) = -T.Θ v := (partnerAdd T).map_neg v

theorem partner_real_smul (T : Partner H) (r : ℝ) (v : H) : T.Θ (r • v) = r • T.Θ v := by
  have h := T.map_smul (r : ℂ) v
  simp only [Complex.star_def, Complex.conj_ofReal] at h
  simpa only [Complex.coe_smul] using h

/-- **Definition 3, in every orthonormal basis:** the matrix of the quaternionic structure,
`J_b i j = ⟪b i, Θ (b j)⟫`, so that `Θ v = J_b v̄` in the coordinates of `b`. -/
noncomputable def partnerMatrix (T : Partner H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ⟪b i, T.Θ (b j)⟫_ℂ

/-! ## Definition 4: the distinctions of every system -/

/-- **Definition 4:** the real space `Q` of the distinctions of `(H, Θ)`: self-adjoint operators of
trace zero that commute with the quaternionic structure. -/
def distinctionsH [FiniteDimensional ℂ H] (T : Partner H) : Submodule ℝ (H →ₗ[ℂ] H) where
  carrier := {a | T.IsDistinctionH a}
  add_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨ha1.add hb1, by rw [map_add, ha2, hb2, add_zero], fun v => ?_⟩
    simp only [LinearMap.add_apply, ha3, hb3, T.map_add]
  zero_mem' := ⟨IsSelfAdjoint.zero _, by simp, fun v => by simp [partner_zero T]⟩
  smul_mem' r a ha := by
    obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨(IsSelfAdjoint.all r).smul h1, ?_, fun v => ?_⟩
    · rw [← Complex.coe_smul, map_smul, h2, smul_zero]
    · rw [← Complex.coe_smul, LinearMap.smul_apply, LinearMap.smul_apply, h3, Complex.coe_smul,
        Complex.coe_smul, partner_real_smul]

theorem mem_distinctionsH [FiniteDimensional ℂ H] (T : Partner H) (a : H →ₗ[ℂ] H) :
    a ∈ distinctionsH T ↔ T.IsDistinctionH a := Iff.rfl

/-- The distinctions of a candidate system are `distinctionsH` of its conjugate. -/
theorem candidate_Q_eq (S : CandidateSystem) : S.Q = distinctionsH S.partner :=
  Submodule.ext fun _ => Iff.rfl

/-- **Definition 4:** the normalized trace `τ(X) = Tr X / dim H` on every system. -/
noncomputable def τH [FiniteDimensional ℂ H] (X : H →ₗ[ℂ] H) : ℂ :=
  LinearMap.trace ℂ H X / (finrank ℂ H : ℂ)

end Partner

/-! ## Definition 5: the ordered products of lines -/

/-- **Definition 5:** for a set `S = {s₁ < ⋯ < s_r}` of lines, `γ_S = γ_{s₁}⋯γ_{s_r}`, `γ_∅ = 1`. -/
noncomputable abbrev gammaS (S : Finset (Fin 5)) : Matrix Four Four ℂ := gammaD S

/-! ## Definition 7: the rotations -/

/-- **Definition 7:** the rotations of one system, unitary of determinant one. -/
abbrev SU4 := Matrix.specialUnitaryGroup Four ℂ

/-! ## Definitions 8 and 11: the matrix of a two-spinor state, and the count of disagreement -/

/-- **Definition 8:** the matrix `M_v` of the two-spinor state `v = Σ M_xy u_x ⊗ u_y`. -/
def relMat (v : Two → ℂ) : Matrix Four Four ℂ := Matrix.of fun x y => v (x, y)

theorem relOf_relMat (v : Two → ℂ) : relOf (relMat v) = v := by
  funext p
  rfl

theorem relMat_relOf (M : Matrix Four Four ℂ) : relMat (relOf M) = M := by
  ext x y
  rfl

/-- **Definition 11:** `N = Σ_t n_t`, the number of lines on which two systems disagree. -/
noncomputable def Ncount : Matrix Two Two ℂ := ∑ t, count t

/-! ## Definition 12: the six directions -/

/-- **Definition 12:** the six directions, the antisymmetric two-spinor states of two systems. -/
def sixDirections : Submodule ℂ (Two → ℂ) where
  carrier := {v | swap *ᵥ v = -v}
  add_mem' {v w} hv hw := by
    show swap *ᵥ (v + w) = -(v + w)
    rw [Matrix.mulVec_add, hv, hw, neg_add]
  zero_mem' := by
    show swap *ᵥ 0 = -0
    simp
  smul_mem' c v hv := by
    show swap *ᵥ (c • v) = -(c • v)
    rw [Matrix.mulVec_smul, hv, smul_neg]

/-- **Definition 12:** the Pfaffian of a two-spinor state, `p(v) = Pf M_v / Pf M_Ω`. -/
noncomputable def pfRel (v : Two → ℂ) : ℂ := pf (relMat v) / pf MΩ

/-- **Definition 12:** P1's real six, the six directions on which the Pfaffian is the length,
`p(v) = ‖v‖²`. -/
def P1six : Set (Two → ℂ) := {v | v ∈ sixDirections ∧ pfRel v = star v ⬝ᵥ v}

/-- **Definition 12:** P3's real six, the six directions that the quaternionic structures of both systems leave
unchanged, `(Θ ⊗ Θ)v = v`. -/
def P3six : Set (Two → ℂ) := {v | v ∈ sixDirections ∧ Comparison.Article.thetaTwo v = v}

/-! ## Definition 13: divisions -/

/-- **Definition 13:** a division of P1's real six, given by its divided part `D` (a subspace of the
real six `E6`, in the basis `f₀ = J`, `f_{s+1} = iγ_sJ`); the undivided part is `Dᗮ`, and gauge `Dᗮ`
divided is the same division. -/
abbrev Division := Submodule ℝ GroupsContinuumLaw.E6

namespace Division

/-- The sign of a division: `+1` on the undivided part `Dᗮ`, `−1` on the divided part `D`. -/
noncomputable def sign (D : Division) : GroupsContinuumLaw.E6 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E6 := Dᗮ.reflection

/-- Two divided parts name the same division when one is the other's complement. -/
def Same (D D' : Division) : Prop := D' = D ∨ D' = Dᗮ

/-- The type `k | 6 − k`: `k` the dimension of the smaller part. -/
noncomputable def kind (D : Division) : ℕ := min (finrank ℝ D) (6 - finrank ℝ D)

/-- A division holds the singlet when the singlet lies wholly in one part. -/
def HoldsSinglet (D : Division) : Prop := GroupsContinuumLaw.e0 ∈ D ∨ GroupsContinuumLaw.e0 ∈ Dᗮ

/-- In a basis a division is a set `D ⊆ Fin 6` of divided directions. -/
noncomputable def ofSet (D : Finset (Fin 6)) : Division :=
  Submodule.span ℝ ((fun a => EuclideanSpace.single a (1 : ℝ)) '' (D : Set (Fin 6)))

end Division

/-! ## Definition 14: the square root of the sign -/

/-- **Definition 14:** the square root of the sign of the division whose divided part has the projector `P`:
`q = (1 − P) + iP`, one on the undivided part and `i` on the divided part. -/
noncomputable def halfOf {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) :
    Matrix n n ℂ :=
  1 - P.map (↑) + Complex.I • P.map (↑)

/-! ## Definition 15: metric, kept and moved, balanced directions, the real form -/

/-- The Pfaffian of P1's real six in its coordinates: `p(z) = Σ z_a²` (`GroupsContinuumLaw.pf_ιC`). -/
def pSix (z : Fin 6 → ℂ) : ℂ := ∑ a, z a ^ 2

/-- **Definition 15:** the metric of a division, `g_D(v) = p(q_D v)` on P1's real six. -/
noncomputable def metricOf (P : Matrix (Fin 6) (Fin 6) ℝ) (v : Fin 6 → ℝ) : ℂ :=
  pSix (halfOf P *ᵥ fun a => (v a : ℂ))

/-- The sign of the division with projector `P`, `θ = 1 − 2P`. -/
def signOf (P : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 6) (Fin 6) ℝ := 1 - (2 : ℝ) • P

/-- **Definition 15:** a generator `X` of rotations of P1's real six is kept by the division when it
commutes with the sign. -/
def KeptBy (P X : Matrix (Fin 6) (Fin 6) ℝ) : Prop := X * signOf P = signOf P * X

/-- **Definition 15:** moved when it anticommutes with the sign. -/
def MovedBy (P X : Matrix (Fin 6) (Fin 6) ℝ) : Prop := X * signOf P = -(signOf P * X)

/-- **Definition 15:** a balanced direction: `v ≠ 0` with `g_D(v) = 0` (taken up to a real factor). -/
def Balanced (P : Matrix (Fin 6) (Fin 6) ℝ) (v : Fin 6 → ℝ) : Prop := v ≠ 0 ∧ metricOf P v = 0

/-- The image of P1's real six under the square root of the sign: the two-spinor state matrices `ι(q z)`, `z` real. -/
def halfSix (P : Matrix (Fin 6) (Fin 6) ℝ) : Set (Matrix Four Four ℂ) :=
  {A | ∃ t : Fin 6 → ℝ, A = GroupsContinuumLaw.ιC (halfOf P *ᵥ fun a => (t a : ℂ))}

/-- **Definition 15:** the generators of the real form: trace zero, and `X ⊗ 1 + 1 ⊗ X`
(`A ↦ XA + AXᵀ` on the two-spinor state matrices) keeps `q_D(P1's real six)`. -/
def realFormAlg (P : Matrix (Fin 6) (Fin 6) ℝ) : Set (Matrix Four Four ℂ) :=
  {X | X.trace = 0 ∧ ∀ A ∈ halfSix P, act X A ∈ halfSix P}

/-- **Definition 15:** the real form of a division, the group generated by the `e^X`, `X` in
`realFormAlg`. -/
noncomputable def realForm (P : Matrix (Fin 6) (Fin 6) ℝ) : Subgroup (Matrix Four Four ℂ)ˣ :=
  Subgroup.closure {U | ∃ X ∈ realFormAlg P, (U : Matrix Four Four ℂ) = NormedSpace.exp X}

/-! ## Definition 16: the sixty-four sets -/

/-- The six directions as `ℂ⁶`, coordinates in the basis `f₀ = Ω, f₁, …, f₅`. -/
abbrev Six := Fin 6 → ℂ

/-- The basis vector `f_a` of the six. -/
def fvec (a : Fin 6) : Six := Pi.single a 1

/-- **Definition 16:** for `S ⊆ {0, …, 5}`, `f_S` is the exterior product of the `f_a`, `a ∈ S`, in
increasing order; the sixty-four `f_S` span the exterior algebra of the six. -/
noncomputable def fS (S : Finset (Fin 6)) : ExteriorAlgebra ℂ Six :=
  ExteriorAlgebra.ιMulti ℂ S.card (fun k => fvec (S.orderEmbOfFin rfl k))

end Geometry

end Comparison.System
