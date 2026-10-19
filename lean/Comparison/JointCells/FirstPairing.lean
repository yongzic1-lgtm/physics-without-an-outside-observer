import Comparison.Existence.Spin
import Comparison.Existence.Turn

/-!
# The first pairing's joint cell

In the first pairing P5 breaks, the line holding a division `D` of the six, and P4 completes it at
every vertex, vertically and in parallel. The one step that exists is Proposition 37's joint step
`𝒯 = J(a)Λ(U)`; with the square root of the sign of the held division the vertical step along `x` is
`f_x = i^{[x ∈ D]} J_x` (`halfStep`, Proposition 34). This file writes the joint cell for every
division `D` of the six at once, so for the four types `0|6, 1|5, 2|4, 3|3` together.

**The joint step of a plane** (`joint_split`): two square-root steps are one generator of their plane and a change
of two directions, `f_x f_y = i^{[x∈D]+[y∈D]} (T_xy + ε_xε_y + ι_xι_y)`.

* **Its parallel projection** (`joint_parallel`): the part that keeps the number of divided
  directions is `X = i^{[x∈D]+[y∈D]} T_xy` (`parTurn`), the generator of the plane (Proposition 36).
* **Its vertical projection** (`joint_loop`): the loop `(f_x f_y)² = −θ_D(x)θ_D(y)`, `−1` on the
  planes within a side and `+1` across (Proposition 34); the whole `f₀⋯f₅ = i^{|D|} w` squares to
  `(−1)^{|D|+1}` (`whole_sq`, Propositions 35, 86).
* **The two at once** (`parTurn_cube`): `X³ = (f_x f_y)² X`. The generator's cube is the plane's loop
  times the generator: where the loop returns `−1` the generator is a rotation (`X³ = −X`, a kept generator), where
  it returns `+1` it is a boost (`X³ = X`, a moved generator). `loop_kept_iff`: the loop is `−1` exactly
  on the planes the division keeps.
* **The frame P4 holds** (`commute_quarter_iff`, `kept_carries_half`): a matrix commutes with the square
  root of the sign `q_D` exactly when it commutes with the sign `θ_D`, and an orthogonal one that does carries
  the square-root step, `Λ(O) f^D(a) Λ(O)⁻¹ = f^D(Oa)`.

**The own clock** (`own_clock_moved`, `own_clock_kept_out`, `own_clock_kept_in`): on the plane of the
singlet and a line `t`, `f_n f_t` is the step of one system along `t`, `γ_t = iJ_nJ_t` (Proposition 37),
exactly where `D` moves the line's own clock (one of `n, t` divided), and the quarter turn
`∓iγ_t = e^{∓i(π/2)γ_t}` of that clock (Proposition 41) where `D` keeps it. `steps_clifford`: the five
`γ_t` anticommute and square to one. `step_at_own`, `step_at_singlet_twin`: at the line's own division
`{t}` and at the singlet's counterpart `{n}` the joint step of `(n t)` is `γ_t` itself.

**The six divisions a line holds** (`moved_clocks_held`, Proposition 27): the moved own clocks are
none at `{}`, all five at `{n}`, the four other lines at `{h, n}`, `h` at `{h}`, `h, k` at `F` and the
colour lines at `C` (Propositions 173, 192); `twin_exchanges`: toggling the singlet exchanges the kept and
the moved own clocks at every division.

Directions: `0 = n`, `1 = h`, `2 = k`, `3, 4, 5 = c₁, c₂, c₃`.
-/

open Comparison Finset Matrix

namespace Comparison.JointCells

/-! ## The square root of the sign on each direction -/

/-- The square root of the sign on one direction: `i` on the divided directions, `1` on the others. -/
noncomputable def quarter (D : Finset (Fin 6)) (x : Fin 6) : ℂ := if x ∈ D then Complex.I else 1

/-- The sign of the division on a direction: `θ_D(x) = −1` on `D`, `+1` off it. -/
def sgn (D : Finset (Fin 6)) (x : Fin 6) : ℂ := if x ∈ D then -1 else 1

theorem quarter_sq (D : Finset (Fin 6)) (x : Fin 6) : quarter D x * quarter D x = sgn D x := by
  unfold quarter sgn
  split_ifs <;> simp [Complex.I_mul_I]

theorem halfStep_eq (D : Finset (Fin 6)) (x : Fin 6) : halfStep D x = quarter D x • Jx x := rfl

/-! ## The joint step of a plane and its two projections -/

/-- **The joint step of a plane:** two square-root steps are one generator of their plane and a change of two
directions, `f_x f_y = i^{[x∈D]+[y∈D]} (T_xy + ε_xε_y + ι_xι_y)`. -/
theorem joint_split (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    halfStep D x * halfStep D y =
      (quarter D x * quarter D y) • (Tx x y + εx x * εx y + ιx x * ιx y) := by
  rw [halfStep_eq, halfStep_eq, smul_mul_smul_comm, Jx_mul_Jx hxy]

/-- The parallel part of the joint step: `X = i^{[x∈D]+[y∈D]} T_xy`. -/
noncomputable def parTurn (D : Finset (Fin 6)) (x y : Fin 6) :
    Module.End ℂ (Finset (Fin 6) → ℂ) :=
  (quarter D x * quarter D y) • Tx x y

/-- **The parallel projection:** the part of two square-root steps that keeps the number of divided
directions is the generator of their plane, `Σ_k Π_k f_x f_y Π_k = i^{[x∈D]+[y∈D]} T_xy`. -/
theorem joint_parallel (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    ∑ k ∈ Finset.range 7, degreeProj k * (halfStep D x * halfStep D y) * degreeProj k =
      parTurn D x y := by
  rw [halfStep_eq, halfStep_eq, smul_mul_smul_comm, parTurn, Tx_eq_sum_degrees hxy,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]

/-- **The vertical projection, the loop:** `(f_x f_y)² = −θ_D(x)θ_D(y)`. -/
theorem joint_loop (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    (halfStep D x * halfStep D y) * (halfStep D x * halfStep D y) =
      (-(sgn D x * sgn D y)) • 1 := by
  rw [half_loop_sq D hxy]
  rfl

/-- **The two at once:** `X³ = (f_x f_y)² X`, the generator's cube is the plane's loop times the generator. -/
theorem parTurn_cube (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    parTurn D x y * parTurn D x y * parTurn D x y = (-(sgn D x * sgn D y)) • parTurn D x y := by
  have hc : (quarter D x * quarter D y) * (quarter D x * quarter D y) = sgn D x * sgn D y := by
    rw [← quarter_sq D x, ← quarter_sq D y]
    ring
  simp only [parTurn, smul_mul_smul_comm, Tx_cube hxy, smul_neg, smul_smul]
  rw [← neg_smul]
  congr 1
  linear_combination (-(quarter D x * quarter D y)) * hc

/-- `X³ = (f_x f_y)² X` written with the loop itself. -/
theorem parTurn_cube_loop (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    parTurn D x y * parTurn D x y * parTurn D x y =
      ((halfStep D x * halfStep D y) * (halfStep D x * halfStep D y)) * parTurn D x y := by
  rw [parTurn_cube D hxy, joint_loop D hxy, smul_mul_assoc, one_mul]

/-- **Kept exactly where the loop is `−1`:** the loop is `−1` on the planes within a side
(`θ_D(x) = θ_D(y)`, kept generators) and `+1` on the planes across (moved generators). -/
theorem loop_kept_iff (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    (halfStep D x * halfStep D y) * (halfStep D x * halfStep D y) =
      (if (x ∈ D ↔ y ∈ D) then (-1 : ℂ) else 1) • 1 := by
  rw [joint_loop D hxy]
  congr 1
  unfold sgn
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp [hx, hy]

/-- The generator is a rotation (`X³ = −X`) on a kept plane. -/
theorem parTurn_rotation (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) (h : x ∈ D ↔ y ∈ D) :
    parTurn D x y * parTurn D x y * parTurn D x y = -parTurn D x y := by
  have hs : sgn D x * sgn D y = 1 := by
    unfold sgn
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp_all
  rw [parTurn_cube D hxy, hs]
  exact neg_one_smul ℂ (parTurn D x y)

/-- The generator is a boost (`X³ = X`) on a moved plane. -/
theorem parTurn_boost (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) (h : ¬(x ∈ D ↔ y ∈ D)) :
    parTurn D x y * parTurn D x y * parTurn D x y = parTurn D x y := by
  rw [parTurn_cube D hxy]
  unfold sgn
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp_all

/-- **The whole:** `f₀ ⋯ f₅ = i^{|D|} w` squares to `(−1)^{|D|+1}`: a phase at even `|D|`, a scale
at odd `|D|` (Propositions 35, 86). -/
theorem whole_sq (D : Finset (Fin 6)) :
    (List.ofFn (halfStep D)).prod * (List.ofFn (halfStep D)).prod = ((-1 : ℂ) ^ (D.card + 1)) • 1 := by
  rw [half_prod, smul_mul_smul_comm, volume_sq, ← pow_add, ← two_mul, pow_mul, Complex.I_sq,
    smul_neg, ← neg_smul, pow_succ]
  congr 1
  ring

/-! ## The frame P4 holds: the generators that carry the square root of the sign are the generators the division keeps -/

theorem mixed_q1 (z : ℂ) : z * 1 = Complex.I * z ↔ z = 0 := by
  constructor
  · intro h
    have h' : z * (1 - Complex.I) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact h0
    · exfalso
      have := congrArg Complex.re h0
      simp at this
  · intro h
    simp [h]

theorem mixed_s1 (z : ℂ) : z * 1 = -1 * z ↔ z = 0 := by
  constructor
  · intro h
    have h' : (2 : ℂ) * z = 0 := by linear_combination h
    simpa using h'
  · intro h
    simp [h]

theorem mixed_q2 (z : ℂ) : z * Complex.I = 1 * z ↔ z = 0 := by
  rw [mul_comm, one_mul, eq_comm, ← mixed_q1 z, mul_one, eq_comm]

theorem mixed_s2 (z : ℂ) : z * -1 = 1 * z ↔ z = 0 := by
  rw [mul_comm, one_mul, eq_comm, ← mixed_s1 z, mul_one, eq_comm]

/-- **A matrix commutes with the square root of the sign `q_D` exactly when it commutes with the sign `θ_D`:** the generators
that carry the square root of the sign are the generators the division keeps (Definition 15). -/
theorem commute_quarter_iff (D : Finset (Fin 6)) (O : Matrix (Fin 6) (Fin 6) ℂ) :
    O * diagonal (quarter D) = diagonal (quarter D) * O ↔
      O * diagonal (sgn D) = diagonal (sgn D) * O := by
  have key : ∀ a b : Fin 6,
      (O a b * quarter D b = quarter D a * O a b ↔ O a b * sgn D b = sgn D a * O a b) := by
    intro a b
    unfold quarter sgn
    by_cases ha : a ∈ D <;> by_cases hb : b ∈ D
    · simp only [ha, hb, ↓reduceIte]
      constructor <;> intro _ <;> ring
    · simp only [ha, hb, ↓reduceIte]
      rw [mixed_q1, mixed_s1]
    · simp only [ha, hb, ↓reduceIte]
      rw [mixed_q2, mixed_s2]
    · simp only [ha, hb, ↓reduceIte]
  constructor
  · intro h
    ext a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab ⊢
    exact (key a b).mp hab
  · intro h
    ext a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab ⊢
    exact (key a b).mpr hab

/-- The square-root step along a vector of the six: `f^D(a) = J(q_D a)`. -/
noncomputable def halfVec (D : Finset (Fin 6)) (a : Fin 6 → ℂ) : Module.End ℂ (Finset (Fin 6) → ℂ) :=
  Jv (diagonal (quarter D) *ᵥ a)

theorem Jv_smul_c (c : ℂ) (v : Fin 6 → ℂ) : Jv (c • v) = c • Jv v := by
  rw [Jv, Jv, εv_smul, ιv_smul, smul_add]

theorem Jv_single_c (x : Fin 6) : Jv (R := ℂ) (Pi.single x 1) = Jx x := by
  rw [Jv, εv_single, ιv_single]
  rfl

theorem diag_single (D : Finset (Fin 6)) (x : Fin 6) :
    diagonal (quarter D) *ᵥ Pi.single x 1 = quarter D x • (Pi.single x 1 : Fin 6 → ℂ) := by
  funext i
  by_cases h : i = x
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, h]

/-- The square-root step along a direction of the six is Proposition 34's `f_x`. -/
theorem halfVec_single (D : Finset (Fin 6)) (x : Fin 6) :
    halfVec D (Pi.single x 1) = halfStep D x := by
  rw [halfVec, diag_single, Jv_smul_c, Jv_single_c, halfStep_eq]

/-- **A kept generator carries the square-root step:** for an orthogonal `O` that commutes with the sign of the
division, `Λ(O) f^D(a) Λ(O)⁻¹ = f^D(Oa)`, the joint step of Proposition 37 with the square root of the sign. -/
theorem kept_carries_half (D : Finset (Fin 6)) (O : Matrix (Fin 6) (Fin 6) ℂ) (hO : Oᵀ * O = 1)
    (hk : O * diagonal (sgn D) = diagonal (sgn D) * O) (a : Fin 6 → ℂ) :
    extMap O * halfVec D a * extMap Oᵀ = halfVec D (O *ᵥ a) := by
  have hq := (commute_quarter_iff D O).mpr hk
  rw [halfVec, extMap_conj_Jv O hO, halfVec, Matrix.mulVec_mulVec, hq, ← Matrix.mulVec_mulVec]

/-! ## The own clock: the moved clock is the step itself, the kept clock its quarter turn -/

/-- **The step of one system along `t`** (Proposition 37): `γ_t = i J_n J_t`, `n = 0`. -/
noncomputable def stepOne (t : Fin 6) : Module.End ℂ (Finset (Fin 6) → ℂ) :=
  Complex.I • (Jx 0 * Jx t)

/-- **Where the division moves the own clock** (exactly one of `n, t` divided), the joint step of
the plane `(n t)` is the step of one system along `t` itself: `f_n f_t = γ_t`. -/
theorem own_clock_moved (D : Finset (Fin 6)) (t : Fin 6) (h : ¬((0 : Fin 6) ∈ D ↔ t ∈ D)) :
    halfStep D 0 * halfStep D t = stepOne t := by
  rw [halfStep_eq, halfStep_eq, smul_mul_smul_comm, stepOne]
  congr 1
  unfold quarter
  by_cases h0 : (0 : Fin 6) ∈ D <;> by_cases ht : t ∈ D <;> simp_all

/-- **Where the division keeps the own clock with both undivided**, the joint step is the quarter
turn `−iγ_t = e^{−i(π/2)γ_t}` of the clock. -/
theorem own_clock_kept_out (D : Finset (Fin 6)) (t : Fin 6) (h0 : (0 : Fin 6) ∉ D) (ht : t ∉ D) :
    halfStep D 0 * halfStep D t = (-Complex.I) • stepOne t := by
  rw [halfStep_eq, halfStep_eq, smul_mul_smul_comm, stepOne, smul_smul]
  congr 1
  unfold quarter
  simp [h0, ht, Complex.I_mul_I]

/-- **Where the division keeps the own clock with both divided**, the joint step is the quarter turn
`iγ_t = e^{i(π/2)γ_t}` of the clock. -/
theorem own_clock_kept_in (D : Finset (Fin 6)) (t : Fin 6) (h0 : (0 : Fin 6) ∈ D) (ht : t ∈ D) :
    halfStep D 0 * halfStep D t = Complex.I • stepOne t := by
  rw [halfStep_eq, halfStep_eq, smul_mul_smul_comm, stepOne, smul_smul]
  congr 1
  unfold quarter
  simp [h0, ht]

/-- Two steps of one system along lines `s, t`: `γ_s γ_t = J_s J_t`. -/
theorem stepOne_mul {s : Fin 6} (t : Fin 6) (hs : s ≠ 0) :
    stepOne s * stepOne t = Jx s * Jx t := by
  have h1 : Jx (R := ℂ) s * Jx 0 = (-1 : ℂ) • (Jx 0 * Jx s) := by
    rw [Jx_anticomm hs]
    exact (neg_one_smul ℂ (Jx (R := ℂ) 0 * Jx s)).symm
  have h2 : Jx (R := ℂ) 0 * Jx s * (Jx 0 * Jx t) = (-1 : ℂ) • (Jx s * Jx t) := by
    calc Jx (R := ℂ) 0 * Jx s * (Jx 0 * Jx t) = Jx 0 * (Jx s * Jx 0) * Jx t := by
          simp only [mul_assoc]
      _ = Jx 0 * ((-1 : ℂ) • (Jx 0 * Jx s)) * Jx t := by rw [h1]
      _ = (-1 : ℂ) • (Jx 0 * Jx 0 * Jx s * Jx t) := by
          rw [mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = (-1 : ℂ) • (Jx s * Jx t) := by rw [Jx_mul_self, one_mul]
  unfold stepOne
  rw [smul_mul_smul_comm, h2, smul_smul, Complex.I_mul_I,
    show ((-1 : ℂ) * -1) = 1 by norm_num]
  exact one_smul ℂ (Jx (R := ℂ) s * Jx t)

/-- **The five steps are five lines of one system:** `γ_sγ_t + γ_tγ_s = 2δ_st`. -/
theorem steps_clifford {s t : Fin 6} (hs : s ≠ 0) (ht : t ≠ 0) :
    stepOne s * stepOne t + stepOne t * stepOne s = if s = t then 2 else 0 := by
  rw [stepOne_mul t hs, stepOne_mul s ht]
  exact Jx_anticomm_add s t

/-- **At the line's own division `{t}`** the joint step of `(n t)` is the step along `t`. -/
theorem step_at_own (t : Fin 6) (ht : t ≠ 0) : halfStep {t} 0 * halfStep {t} t = stepOne t := by
  apply own_clock_moved
  simp [Finset.mem_singleton, Ne.symm ht]

/-- **At the singlet's counterpart `{n}`** (P3's own division) the joint steps of the five planes `(n t)`
are the five steps of one system. -/
theorem step_at_singlet_twin (t : Fin 6) (ht : t ≠ 0) :
    halfStep {0} 0 * halfStep {0} t = stepOne t := by
  apply own_clock_moved
  simp [Finset.mem_singleton, ht]

/-! ## The clock at `2|4`: the divided plane's generator commutes with the kept generators outside it -/

/-- **At a division of two directions `{a, b}`** the generator of the divided plane commutes with the
generator of every plane outside it, the kept generators of the other side: the clock (Propositions 41, 91). -/
theorem clock_commutes (a b c d : Fin 6) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    parTurn {a, b} a b * parTurn {a, b} c d = parTurn {a, b} c d * parTurn {a, b} a b := by
  unfold parTurn
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (quarter {a, b} a * quarter {a, b} b)]
  congr 1
  exact sub_eq_zero.mp (Tx_comm_disjoint hac had hbc hbd)

/-! ## The six divisions a line holds, and the counterparts -/

/-- The own clocks a division moves: the lines `t` with exactly one of `n, t` divided. -/
def movedClocks (D : Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ.filter fun t => t ≠ 0 ∧ ¬((0 : Fin 6) ∈ D ↔ t ∈ D)

/-- **The moved own clocks at the six divisions a line holds** (Proposition 27): none at `{}`, all
five at `{n}`, the four other lines at `{h, n}`, `h` at `{h}`, `h, k` at `F`, the colour lines at `C`
(Propositions 173, 192). -/
theorem moved_clocks_held :
    movedClocks ∅ = ∅ ∧ movedClocks {0} = {1, 2, 3, 4, 5} ∧ movedClocks {0, 1} = {2, 3, 4, 5} ∧
      movedClocks {1} = {1} ∧ movedClocks {1, 2} = {1, 2} ∧ movedClocks {3, 4, 5} = {3, 4, 5} := by
  decide

/-- **The counterparts exchange time and mass:** toggling the singlet exchanges the kept and the moved own
clocks at every division of the six. -/
theorem twin_exchanges : ∀ D : Finset (Fin 6),
    movedClocks (symmDiff D {0}) = (Finset.univ.filter fun t : Fin 6 => t ≠ 0) \ movedClocks D := by
  decide

/-! ## The joint cell, its two projections at once -/

/-- **The first pairing's joint cell at every division `D`:** for every plane `(x y)` the joint step
splits into the generator and the two-direction change; its grade-keeping projection is the generator `X`; its
loop is `−θ_D(x)θ_D(y)`; and `X³` is the loop times `X`. -/
theorem joint_cell (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    halfStep D x * halfStep D y =
        (quarter D x * quarter D y) • (Tx x y + εx x * εx y + ιx x * ιx y) ∧
      ∑ k ∈ Finset.range 7, degreeProj k * (halfStep D x * halfStep D y) * degreeProj k =
        parTurn D x y ∧
      (halfStep D x * halfStep D y) * (halfStep D x * halfStep D y) = (-(sgn D x * sgn D y)) • 1 ∧
      parTurn D x y * parTurn D x y * parTurn D x y =
        ((halfStep D x * halfStep D y) * (halfStep D x * halfStep D y)) * parTurn D x y :=
  ⟨joint_split D hxy, joint_parallel D hxy, joint_loop D hxy, parTurn_cube_loop D hxy⟩

end Comparison.JointCells

#print axioms Comparison.JointCells.joint_split
#print axioms Comparison.JointCells.joint_parallel
#print axioms Comparison.JointCells.joint_loop
#print axioms Comparison.JointCells.parTurn_cube
#print axioms Comparison.JointCells.parTurn_cube_loop
#print axioms Comparison.JointCells.loop_kept_iff
#print axioms Comparison.JointCells.parTurn_rotation
#print axioms Comparison.JointCells.parTurn_boost
#print axioms Comparison.JointCells.whole_sq
#print axioms Comparison.JointCells.commute_quarter_iff
#print axioms Comparison.JointCells.halfVec_single
#print axioms Comparison.JointCells.kept_carries_half
#print axioms Comparison.JointCells.own_clock_moved
#print axioms Comparison.JointCells.own_clock_kept_out
#print axioms Comparison.JointCells.own_clock_kept_in
#print axioms Comparison.JointCells.stepOne_mul
#print axioms Comparison.JointCells.steps_clifford
#print axioms Comparison.JointCells.step_at_own
#print axioms Comparison.JointCells.step_at_singlet_twin
#print axioms Comparison.JointCells.clock_commutes
#print axioms Comparison.JointCells.moved_clocks_held
#print axioms Comparison.JointCells.twin_exchanges
#print axioms Comparison.JointCells.joint_cell
