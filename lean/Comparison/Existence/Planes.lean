module

public import Comparison.Existence.Walk
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Book XII. The plane contrasts (Proposition 73)

The ten symmetric states are the pairs `a < b` of the
five directions, `planeSet i = {planeA i, planeB i}`, in the order of the two-spinor states `6, …, 15`
(`disagreeSet_planeRel`).

* `plane_step_outside`: from a plane, the step along an outside line `c` lands on the plane of the
  other two outside lines; `plane_step_inside`: along a line of the plane it lands on a vector state.
* `petersen_steps`: two symmetric states are one step apart exactly when they are disjoint; `petersen_degree`:
  three steps at each plane; `petersen_srg`: `A² = 2 − A + J`: the Petersen graph.
* `planeLap_eigen`, `eigV_eigW`: `Δ_F = 3 − A_F` has an integer eigenbasis with eigenvalues
  `0, 2⁵, 5⁴`; `planeLap_charpoly`: over `ℚ`, `det(X − Δ_F) = X (X − 2)⁵ (X − 5)⁴`;
  `contrast_sum`: over the nine contrasts `Σ x^{Δ_F} = 5x² + 4x⁵`.
* `projectors`: `P₀ = J/10`, `P₂ = (4 + 2A − J)/6`, `P₅ = (5 − 5A + J)/15` are the eigenprojectors,
  of traces `1, 5, 4`.
* `actF g`: the relabelling `g` of the lines moves the symmetric states; `planeSet_actF`, `actF_mul`;
  `planeLap_relabel`, `planeLap_comm_perm`: `Δ_F` commutes with every relabelling.
* `fixL`, `fixF`, `chi32 = fixF − fixL`, `chi41 = fixL − 1`: `trace_P0`, `trace_P2`, `trace_P5`: the
  relabellings act on the eigenspaces of `0, 2, 5` with characters `1`, `χ_[3,2]`, `χ_[4,1]`;
  `char_norms`: `Σ_g χ² = 120` for both, and the orthogonality sums: each part is one irreducible.
* `kk g = 120 k(g) = 1 + sgn g + 5χ_[3,2](g)`: `k_sum` `Σ_g k(g) = 1`; `k_values`
  `k(e) = 27/120`, `k(exchange) = 5/120`, `k(5-cycle) = 2/120`, `k(3-cycle) = −3/120`.
  (`k·k = k` is `Idempotent.lean`.)
* `perfect_matchings`: the Petersen graph has exactly six perfect matchings; `T_formula`: the
  relabelling `g` keeps `T(g) = 1 + sgn g·χ_[3,2](g)` of them; `T_values`, `chi32_values`,
  `sgn_values` by class; `k_second_form`:
  `120 k(g) = 1 + sgn g·(5T(g) − 4)`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Finset

/-! ## The symmetric states and their steps -/

/-- The smaller line of the plane `i`. -/
def planeA : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

/-- The larger line of the plane `i`. -/
def planeB : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

/-- The plane `i` as a pair of lines. -/
def planeSet (i : Fin 10) : Finset (Fin 5) := {planeA i, planeB i}

/-- The plane `i` among the sixteen two-spinor states. -/
def planeRel (i : Fin 10) : Fin 16 := ⟨i.val + 6, by omega⟩

theorem disagreeSet_planeRel : ∀ i : Fin 10, disagreeSet (planeRel i) = planeSet i := by
  decide +kernel

/-- The symmetric states are exactly the two-spinor states that disagree on two lines. -/
theorem planeRel_onto : ∀ k : Fin 16, (disagreeSet k).card = 2 ↔ ∃ i, planeRel i = k := by
  decide +kernel

/-- **From a plane, the step along an outside line lands on the plane of the other two outside
lines.** -/
theorem plane_step_outside : ∀ i : Fin 10, ∀ c : Fin 5, c ∉ planeSet i →
    ∃ j, transition c (planeRel i) = planeRel j ∧ planeSet j = univ \ insert c (planeSet i) := by
  decide +kernel

/-- From a plane, the step along one of its own lines lands on a vector state. -/
theorem plane_step_inside : ∀ i : Fin 10, ∀ c ∈ planeSet i,
    (disagreeSet (transition c (planeRel i))).card = 4 := by
  decide +kernel

/-! ## The Petersen graph -/

/-- **Two symmetric states are one step apart exactly when they are disjoint.** -/
theorem petersen_steps : ∀ i j : Fin 10,
    (∃ c, transition c (planeRel i) = planeRel j) ↔ Disjoint (planeSet i) (planeSet j) := by
  decide +kernel

/-- Three steps at each plane. -/
theorem petersen_degree : ∀ i : Fin 10,
    (univ.filter fun j => Disjoint (planeSet i) (planeSet j)).card = 3 := by
  decide +kernel

/-- The adjacency of the symmetric states. -/
def petAdj : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun i j => if Disjoint (planeSet i) (planeSet j) then 1 else 0

/-- The all-ones matrix on the symmetric states. -/
def J10 : Matrix (Fin 10) (Fin 10) ℤ := Matrix.of fun _ _ => 1

/-- **The Petersen graph:** `A² = 2 − A + J` (three neighbours, none in common for neighbours,
one in common otherwise). -/
theorem petersen_srg : petAdj * petAdj = (2 : ℤ) • 1 - petAdj + J10 := by
  decide +kernel

/-! ## The Laplacian of the symmetric states -/

/-- `Δ_F = 3 − A_F`. -/
def planeLapZ : Matrix (Fin 10) (Fin 10) ℤ := (3 : ℤ) • 1 - petAdj

/-- An eigenbasis: the constant, five vectors of eigenvalue `2`, four of eigenvalue `5`. -/
def eigV : Matrix (Fin 10) (Fin 10) ℤ :=
  !![1, 1, 1, 1, 1, 1, 1, 1, 0, 0;
    1, 0, 0, -1, 0, -1, 1, 0, 1, 0;
    1, -1, 0, 0, 0, 0, 1, 0, 0, 1;
    1, 0, -1, 0, -1, 0, 0, -1, -1, -1;
    1, -1, -1, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 0, -1, -1, 0, 0, 1, 0, 1;
    1, 0, 0, 0, 0, -1, -1, 0, -1, -1;
    1, 1, 0, 1, 0, 0, 0, 0, 1, 1;
    1, 0, 1, 0, 0, 1, -1, -1, 0, -1;
    1, 0, 0, 0, 1, 0, -1, -1, -1, 0]

/-- Thirty times the inverse of `eigV`. -/
def eigW : Matrix (Fin 10) (Fin 10) ℤ :=
  !![3, 3, 3, 3, 3, 3, 3, 3, 3, 3;
    5, 5, -15, 5, -5, 5, -5, 5, -5, 5;
    0, 0, 10, -10, -10, 0, 10, 0, 10, -10;
    0, -10, 10, 0, 0, -10, 10, 10, 0, -10;
    5, 5, -5, -5, 5, -5, -5, -5, -5, 15;
    5, -5, -5, 5, 5, 5, -15, -5, 5, 5;
    6, 6, 6, 6, -4, -4, -4, -4, -4, -4;
    6, -4, -4, -4, 6, 6, 6, -4, -4, -4;
    -4, 6, -4, -4, 6, -4, -4, 6, 6, -4;
    -4, -4, 6, -4, -4, 6, -4, 6, -4, 6]

/-- The eigenvalues: `0` once, `2` five times, `5` four times. -/
def eigD : Fin 10 → ℤ := ![0, 2, 2, 2, 2, 2, 5, 5, 5, 5]

theorem planeLap_eigen : planeLapZ * eigV = eigV * diagonal eigD := by
  decide +kernel

theorem eigV_eigW : eigV * eigW = (30 : ℤ) • 1 := by
  decide +kernel

/-- `Δ_F` over the rationals. -/
def planeLap : Matrix (Fin 10) (Fin 10) ℚ := planeLapZ.map (Int.castRingHom ℚ)

/-- **`Δ_F` is diagonalized:** `Δ_F = V D V⁻¹` with `D = diag(0, 2, 2, 2, 2, 2, 5, 5, 5, 5)`. -/
theorem planeLap_diagonalized :
    ∃ V W : Matrix (Fin 10) (Fin 10) ℚ, V * W = 1 ∧
      planeLap = V * (diagonal (fun i => (eigD i : ℚ)) * W) := by
  set f := Int.castRingHom ℚ
  refine ⟨eigV.map f, ((1 : ℚ) / 30) • eigW.map f, ?_, ?_⟩
  · have h := congrArg (fun M => M.map f) eigV_eigW
    simp only [Matrix.map_mul] at h
    rw [Matrix.mul_smul, h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [f]
  · have hVW : eigV.map f * (((1 : ℚ) / 30) • eigW.map f) = 1 := by
      have h := congrArg (fun M => M.map f) eigV_eigW
      simp only [Matrix.map_mul] at h
      rw [Matrix.mul_smul, h]
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [f]
    have hLV : planeLap * eigV.map f = eigV.map f * diagonal (fun i => (eigD i : ℚ)) := by
      have h := congrArg (fun M => M.map f) planeLap_eigen
      simp only [Matrix.map_mul] at h
      rw [show planeLap = planeLapZ.map f from rfl, h, Matrix.diagonal_map (map_zero f)]
      rfl
    calc planeLap = planeLap * (eigV.map f * (((1 : ℚ) / 30) • eigW.map f)) := by
          rw [hVW, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hLV, Matrix.mul_assoc]

open Polynomial in
/-- **The spectrum of `Δ_F`:** `det(X − Δ_F) = X (X − 2)⁵ (X − 5)⁴`: `0` once, `2` five times,
`5` four times. -/
theorem planeLap_charpoly : planeLap.charpoly = X * (X - 2) ^ 5 * (X - 5) ^ 4 := by
  obtain ⟨V, W, hVW, hL⟩ := planeLap_diagonalized
  have hWV : W * V = 1 := mul_eq_one_comm.mp hVW
  rw [hL, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hWV, Matrix.mul_one,
    Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_succ, eigD]
  ring

/-- **The nine contrasts:** over the eigenvalues other than `0`, `Σ x^λ = 5x² + 4x⁵`. -/
theorem contrast_sum {R : Type*} [CommSemiring R] (x : R) :
    ∑ i ∈ univ.filter (fun i : Fin 10 => eigD i ≠ 0), x ^ (eigD i).toNat =
      5 * x ^ 2 + 4 * x ^ 5 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, eigD]
  ring

/-- The eigenprojectors, times `10`, `6` and `15`. -/
def P0Z : Matrix (Fin 10) (Fin 10) ℤ := J10
def P2Z : Matrix (Fin 10) (Fin 10) ℤ := (4 : ℤ) • 1 + (2 : ℤ) • petAdj - J10
def P5Z : Matrix (Fin 10) (Fin 10) ℤ := (5 : ℤ) • 1 - (5 : ℤ) • petAdj + J10

/-- **The eigenprojectors:** `P₀ = J/10`, `P₂ = (4 + 2A − J)/6`, `P₅ = (5 − 5A + J)/15` are
idempotent, orthogonal, add to one, `Δ_F` is `0, 2, 5` on them, and their traces (ranks) are
`1, 5, 4`. Written times `10, 6, 15`. -/
theorem projectors :
    P0Z * P0Z = (10 : ℤ) • P0Z ∧ P2Z * P2Z = (6 : ℤ) • P2Z ∧ P5Z * P5Z = (15 : ℤ) • P5Z ∧
    P0Z * P2Z = 0 ∧ P0Z * P5Z = 0 ∧ P2Z * P5Z = 0 ∧
    (3 : ℤ) • P0Z + (5 : ℤ) • P2Z + (2 : ℤ) • P5Z = (30 : ℤ) • 1 ∧
    planeLapZ * P0Z = 0 ∧ planeLapZ * P2Z = (2 : ℤ) • P2Z ∧ planeLapZ * P5Z = (5 : ℤ) • P5Z ∧
    P0Z.trace = 10 * 1 ∧ P2Z.trace = 6 * 5 ∧ P5Z.trace = 15 * 4 := by
  decide +kernel

/-! ## The relabellings of the lines -/

/-- The plane of the pair `{a, b}`. -/
def pairPlane : Fin 5 → Fin 5 → Fin 10 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 4, 5, 6], ![1, 4, 0, 7, 8], ![2, 5, 7, 0, 9], ![3, 6, 8, 9, 0]]

theorem pairPlane_spec : ∀ a b : Fin 5, a ≠ b → planeSet (pairPlane a b) = {a, b} := by
  decide +kernel

theorem planeA_ne_planeB : ∀ i : Fin 10, planeA i ≠ planeB i := by decide

theorem planeSet_inj : ∀ i j : Fin 10, planeSet i = planeSet j → i = j := by decide +kernel

/-- The relabelling `g` of the lines moves the plane `i` to `actF g i`. -/
def actF (g : Equiv.Perm (Fin 5)) (i : Fin 10) : Fin 10 := pairPlane (g (planeA i)) (g (planeB i))

theorem planeSet_actF (g : Equiv.Perm (Fin 5)) (i : Fin 10) :
    planeSet (actF g i) = (planeSet i).map g.toEmbedding := by
  rw [actF, pairPlane_spec _ _ (g.injective.ne (planeA_ne_planeB i)), planeSet, Finset.map_insert,
    Finset.map_singleton]
  rfl

theorem actF_mul (g h : Equiv.Perm (Fin 5)) (i : Fin 10) :
    actF (g * h) i = actF g (actF h i) := by
  apply planeSet_inj
  rw [planeSet_actF, planeSet_actF, planeSet_actF, Finset.map_map]
  rfl

theorem actF_one (i : Fin 10) : actF 1 i = i := by
  apply planeSet_inj
  rw [planeSet_actF]
  exact Finset.map_refl

theorem actF_inv_actF (g : Equiv.Perm (Fin 5)) (i : Fin 10) : actF g⁻¹ (actF g i) = i := by
  rw [← actF_mul, inv_mul_cancel, actF_one]

theorem actF_actF_inv (g : Equiv.Perm (Fin 5)) (i : Fin 10) : actF g (actF g⁻¹ i) = i := by
  rw [← actF_mul, mul_inv_cancel, actF_one]

theorem actF_inj (g : Equiv.Perm (Fin 5)) {i j : Fin 10} : actF g i = actF g j ↔ i = j := by
  constructor
  · intro h
    rw [← actF_inv_actF g i, h, actF_inv_actF]
  · rintro rfl
    rfl

/-- **`Δ_F` is unchanged by every relabelling of the lines.** -/
theorem planeLap_relabel (g : Equiv.Perm (Fin 5)) (i j : Fin 10) :
    planeLapZ (actF g i) (actF g j) = planeLapZ i j := by
  simp only [planeLapZ, petAdj, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, actF_inj, planeSet_actF, Finset.disjoint_map]

/-- The relabelling `g` as a permutation matrix of the symmetric states. -/
def permF (g : Equiv.Perm (Fin 5)) : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun i j => if actF g j = i then 1 else 0

/-- **`Δ_F` commutes with the relabellings.** -/
theorem planeLap_comm_perm (g : Equiv.Perm (Fin 5)) : planeLapZ * permF g = permF g * planeLapZ := by
  ext i j
  simp only [Matrix.mul_apply, permF, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
    zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h : ∀ k, (actF g k = i) ↔ (k = actF g⁻¹ i) := by
    intro k
    constructor
    · rintro rfl
      rw [actF_inv_actF]
    · rintro rfl
      rw [actF_actF_inv]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← planeLap_relabel g⁻¹ i (actF g j), actF_inv_actF]

/-! ## The characters -/

/-- The lines `g` fixes. -/
def fixL (g : Equiv.Perm (Fin 5)) : ℤ := ((univ.filter fun t => g t = t).card : ℤ)

/-- The symmetric states `g` fixes. -/
def fixF (g : Equiv.Perm (Fin 5)) : ℤ := ((univ.filter fun i => actF g i = i).card : ℤ)

/-- `χ_[3,2] = (planes fixed) − (lines fixed)`. -/
def chi32 (g : Equiv.Perm (Fin 5)) : ℤ := fixF g - fixL g

/-- `χ_[4,1] = (lines fixed) − 1`. -/
def chi41 (g : Equiv.Perm (Fin 5)) : ℤ := fixL g - 1

/-- The sign of a relabelling. -/
def sgn (g : Equiv.Perm (Fin 5)) : ℤ := ((Equiv.Perm.sign g : ℤˣ) : ℤ)

/-- The symmetric states carry `1 + χ_[4,1] + χ_[3,2]`, the lines `1 + χ_[4,1]`. -/
theorem planes_char (g : Equiv.Perm (Fin 5)) :
    fixF g = 1 + chi41 g + chi32 g ∧ fixL g = 1 + chi41 g := by
  unfold chi41 chi32
  constructor <;> ring

/-- **The relabellings on the eigenspace of `0`:** the constant, character `1`. -/
theorem trace_P0 : ∀ g : Equiv.Perm (Fin 5), (P0Z * permF g).trace = 10 * 1 := by
  decide +kernel

/-- **The relabellings on the eigenspace of `2` have the character `χ_[3,2]`.** -/
theorem trace_P2 : ∀ g : Equiv.Perm (Fin 5), (P2Z * permF g).trace = 6 * chi32 g := by
  decide +kernel

/-- **The relabellings on the eigenspace of `5` have the character `χ_[4,1]`.** -/
theorem trace_P5 : ∀ g : Equiv.Perm (Fin 5), (P5Z * permF g).trace = 15 * chi41 g := by
  decide +kernel

/-- **Each part is one irreducible:** `Σ_g χ_[3,2]² = Σ_g χ_[4,1]² = 120`; the two, the
unchanged character and the sign are orthogonal. -/
theorem char_norms :
    ∑ g : Equiv.Perm (Fin 5), chi32 g ^ 2 = 120 ∧ ∑ g : Equiv.Perm (Fin 5), chi41 g ^ 2 = 120 ∧
    ∑ g : Equiv.Perm (Fin 5), chi32 g * chi41 g = 0 ∧ ∑ g : Equiv.Perm (Fin 5), chi32 g = 0 ∧
    ∑ g : Equiv.Perm (Fin 5), chi41 g = 0 ∧ ∑ g : Equiv.Perm (Fin 5), sgn g * chi32 g = 0 ∧
    ∑ g : Equiv.Perm (Fin 5), sgn g * chi41 g = 0 ∧ ∑ g : Equiv.Perm (Fin 5), sgn g = 0 := by
  decide +kernel

/-! ## The idempotent -/

/-- `120 k(g) = 1 + sgn g + 5χ_[3,2](g)`. -/
def kk (g : Equiv.Perm (Fin 5)) : ℤ := 1 + sgn g + 5 * chi32 g

/-- **`Σ_g k(g) = 1`.** -/
theorem k_sum : ∑ g : Equiv.Perm (Fin 5), kk g = 120 := by
  decide +kernel

/-- An exchange, a 3-cycle, a 4-cycle and a 5-cycle of the lines. -/
def exch : Equiv.Perm (Fin 5) := Equiv.swap 0 1
def cyc3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
def cyc4 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
def cyc5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
def exch2 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
def cyc3exch : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4

/-- **The values:** `k(e) = 27/120 = 9/40`, `k(exchange) = 5/120 = 1/24`, `k(5-cycle) = 2/120 = 1/60`,
`k(3-cycle) = −3/120 = −1/40`. -/
theorem k_values : kk 1 = 27 ∧ kk exch = 5 ∧ kk cyc5 = 2 ∧ kk cyc3 = -3 := by
  decide +kernel

/-! ## The perfect matchings of the Petersen graph -/

/-- The fifteen edges of the Petersen graph, as pairs of symmetric states. -/
def edgeEnds : Fin 15 → Fin 10 × Fin 10 :=
  ![(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8), (3, 4), (3, 5), (3, 7),
    (4, 9), (5, 8), (6, 7)]

theorem edges_are_steps : ∀ i j : Fin 10, i < j →
    (Disjoint (planeSet i) (planeSet j) ↔ ∃ e, edgeEnds e = (i, j)) := by
  decide +kernel

/-- The plane `i` is an end of the edge `e`. -/
def OnEdge (i : Fin 10) (e : Fin 15) : Prop := (edgeEnds e).1 = i ∨ (edgeEnds e).2 = i

instance (i : Fin 10) : DecidablePred (OnEdge i) := fun e => by
  unfold OnEdge
  infer_instance

/-- A perfect matching: every plane is an end of exactly one of its edges. -/
def IsPerfectMatching (S : Finset (Fin 15)) : Prop := ∀ i : Fin 10, (S.filter (OnEdge i)).card = 1

instance : DecidablePred IsPerfectMatching := fun S => by
  unfold IsPerfectMatching
  infer_instance

theorem ends_two : ∀ e : Fin 15, (univ.filter fun i => OnEdge i e).card = 2 := by
  decide +kernel

/-- A perfect matching has five edges. -/
theorem card_of_perfect {S : Finset (Fin 15)} (hS : IsPerfectMatching S) : S.card = 5 := by
  have h1 : ∑ i : Fin 10, (S.filter (OnEdge i)).card = 10 := by
    have h : ∀ i : Fin 10, (S.filter (OnEdge i)).card = 1 := hS
    simp [h]
  have h2 : ∑ i : Fin 10, (S.filter (OnEdge i)).card =
      ∑ e ∈ S, (univ.filter fun i => OnEdge i e).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h2] at h1
  simp only [ends_two, Finset.sum_const, smul_eq_mul] at h1
  omega

/-- The six perfect matchings. -/
def matchings : Finset (Finset (Fin 15)) :=
  {{0, 4, 8, 10, 12}, {0, 5, 7, 9, 13}, {1, 3, 7, 11, 12}, {1, 5, 6, 10, 14}, {2, 3, 8, 9, 14},
    {2, 4, 6, 11, 13}}

theorem perfect_five :
    ((univ : Finset (Fin 15)).powersetCard 5).filter IsPerfectMatching = matchings := by
  decide +kernel

/-- **The Petersen graph has exactly six perfect matchings.** -/
theorem perfect_matchings (S : Finset (Fin 15)) : IsPerfectMatching S ↔ S ∈ matchings := by
  rw [← perfect_five, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · intro h
    exact ⟨⟨Finset.subset_univ S, card_of_perfect h⟩, h⟩
  · exact fun h => h.2

/-- The edge between two adjacent symmetric states. -/
def edgeIdx : Fin 10 → Fin 10 → Fin 15 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 2],
    ![0, 0, 0, 0, 0, 3, 4, 0, 0, 5],
    ![0, 0, 0, 0, 6, 0, 7, 0, 8, 0],
    ![0, 0, 0, 0, 9, 10, 0, 11, 0, 0],
    ![0, 0, 6, 9, 0, 0, 0, 0, 0, 12],
    ![0, 3, 0, 10, 0, 0, 0, 0, 13, 0],
    ![0, 4, 7, 0, 0, 0, 0, 14, 0, 0],
    ![0, 0, 0, 11, 0, 0, 14, 0, 0, 0],
    ![1, 0, 8, 0, 0, 13, 0, 0, 0, 0],
    ![2, 5, 0, 0, 12, 0, 0, 0, 0, 0]]

/-- The relabelling `g` moves the edge `e`. -/
def actE (g : Equiv.Perm (Fin 5)) (e : Fin 15) : Fin 15 :=
  edgeIdx (actF g (edgeEnds e).1) (actF g (edgeEnds e).2)

/-- The matchings `g` keeps. -/
def keptMatchings (g : Equiv.Perm (Fin 5)) : ℤ :=
  ((matchings.filter fun S => S.image (actE g) = S).card : ℤ)

/-- **`T(g) = 1 + sgn g·χ_[3,2](g)`:** the relabellings permute the six matchings with the
character `1 + χ_[2,2,1]`. -/
theorem T_formula : ∀ g : Equiv.Perm (Fin 5), keptMatchings g = 1 + sgn g * chi32 g := by
  decide +kernel

/-- On the identity, an exchange, two exchanges, a 3-cycle, a 3-cycle with an exchange, a 4-cycle
and a 5-cycle: `T = 6, 0, 2, 0, 0, 2, 1`, `χ_[3,2] = 5, 1, 1, −1, 1, −1, 0`, `sgn = +, −, +, +, −, −, +`. -/
theorem T_values :
    keptMatchings 1 = 6 ∧ keptMatchings exch = 0 ∧ keptMatchings exch2 = 2 ∧
    keptMatchings cyc3 = 0 ∧ keptMatchings cyc3exch = 0 ∧ keptMatchings cyc4 = 2 ∧
    keptMatchings cyc5 = 1 := by
  decide +kernel

theorem chi32_values :
    chi32 1 = 5 ∧ chi32 exch = 1 ∧ chi32 exch2 = 1 ∧ chi32 cyc3 = -1 ∧ chi32 cyc3exch = 1 ∧
    chi32 cyc4 = -1 ∧ chi32 cyc5 = 0 := by
  decide +kernel

theorem sgn_values :
    sgn 1 = 1 ∧ sgn exch = -1 ∧ sgn exch2 = 1 ∧ sgn cyc3 = 1 ∧ sgn cyc3exch = -1 ∧
    sgn cyc4 = -1 ∧ sgn cyc5 = 1 := by
  decide +kernel

theorem sgn_sq (g : Equiv.Perm (Fin 5)) : sgn g * sgn g = 1 := by
  unfold sgn
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- **The second form:** `120 k(g) = 1 + sgn g·(5T(g) − 4)`. -/
theorem k_second_form (g : Equiv.Perm (Fin 5)) :
    kk g = 1 + sgn g * (5 * keptMatchings g - 4) := by
  rw [T_formula, kk]
  have h := sgn_sq g
  linear_combination (-5 * chi32 g) * h

end Comparison

end
