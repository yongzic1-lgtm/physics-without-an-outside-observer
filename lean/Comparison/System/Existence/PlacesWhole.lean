import Comparison.System.Existence.Six
import Comparison.System.Existence.Holonomy4

/-!
# The proof system, the existence layer: Propositions 34, 38 and 39 whole

Prop. 34: the loop signs are the kept and moved rotations, `Kept D x ↔
(the plane of x lies on one side of D)` (`kept_iff`). Prop. 38: `log hol = Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³)` uniformly in
the four rotations (`bch_uniform`, `Holonomy4.lean`). Prop. 39: near one the transport is `U = e^A`, and
`DP = e^A P(y) e^{Aᵀ} − P(x) = (P(y) − P(x)) + (AP(y) + P(y)Aᵀ) + O(‖A‖²)` (`covDiff_exp`), the commutator `[A, P(y)]`
for a rotation `Aᵀ = −A`.
-/

namespace Comparison.System.Existence

open Asymptotics Filter NormedSpace Topology Matrix

/-! ## The transport near one -/

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem transpose_isBigO {n : ℕ} {α : Type*} {l : Filter α} {f : α → Matrix (Fin n) (Fin n) ℝ} {g : α → ℝ}
    (h : f =O[l] g) : (fun x => (f x)ᵀ) =O[l] g := by
  let T : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap
  have hT : ∀ M, T M = Mᵀ := fun M => rfl
  exact ((T.isBigO_comp f l).trans h).congr_left fun x => hT (f x)

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **The transport near one:** `e^A P(y) e^{Aᵀ} − P(x) = (P(y) − P(x)) + (AP(y) + P(y)Aᵀ) + O(‖A‖²)`. -/
theorem covDiff_exp {n : ℕ} (Px Py : Matrix (Fin n) (Fin n) ℝ) :
    (fun A : Matrix (Fin n) (Fin n) ℝ => covDiff (NormedSpace.exp A) Px Py - ((Py - Px) + (A * Py + Py * Aᵀ)))
      =O[𝓝 0] fun A => ‖A‖ ^ 2 := by
  set E : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ := fun A => NormedSpace.exp A - (1 + A) with hE
  have hE2 : E =O[𝓝 0] fun A => ‖A‖ ^ 2 := exp_first_order
  have hE2t : (fun A => (E A)ᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 := transpose_isBigO hE2
  have hA1 : (fun A : Matrix (Fin n) (Fin n) ℝ => A) =O[𝓝 0] fun A => ‖A‖ :=
    isBigO_norm_right.mpr (isBigO_refl _ _)
  have hA1t : (fun A : Matrix (Fin n) (Fin n) ℝ => Aᵀ) =O[𝓝 0] fun A => ‖A‖ := transpose_isBigO hA1
  have cPy := isBigO_const_one ℝ Py (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ))
  have t1 : (fun A => Py * (E A)ᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 := (cPy.mul hE2t).congr_right fun A => one_mul _
  have t2 : (fun A : Matrix (Fin n) (Fin n) ℝ => A * Py * Aᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 :=
    ((hA1.mul cPy).mul hA1t).congr_right fun A => by ring
  have t3 : (fun A => A * Py * (E A)ᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 :=
    (((hA1.mul cPy).mul hE2t).congr_right fun A => by ring).trans (pow_isBigO_pow (m := 3) (k := 2) (by norm_num))
  have t4 : (fun A => E A * Py) =O[𝓝 0] fun A => ‖A‖ ^ 2 := (hE2.mul cPy).congr_right fun A => mul_one _
  have t5 : (fun A => E A * Py * Aᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 :=
    (((hE2.mul cPy).mul hA1t).congr_right fun A => by ring).trans (pow_isBigO_pow (m := 3) (k := 2) (by norm_num))
  have t6 : (fun A => E A * Py * (E A)ᵀ) =O[𝓝 0] fun A => ‖A‖ ^ 2 :=
    (((hE2.mul cPy).mul hE2t).congr_right fun A => by ring).trans (pow_isBigO_pow (m := 4) (k := 2) (by norm_num))
  refine (((((t1.add t2).add t3).add t4).add t5).add t6).congr_left fun A => ?_
  have hexp : NormedSpace.exp A = 1 + A + E A := by
    simp only [hE]
    abel
  simp only [covDiff]
  rw [hexp, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **The transport near one, along the rotations:** for `Aᵀ = −A`,
`e^A P(y) e^{−A} − P(x) = (P(y) − P(x)) + [A, P(y)] + O(‖A‖²)`. -/
theorem covDiff_exp_turn {n : ℕ} (Px Py : Matrix (Fin n) (Fin n) ℝ) :
    (fun A : Matrix (Fin n) (Fin n) ℝ => covDiff (NormedSpace.exp A) Px Py - ((Py - Px) + (A * Py - Py * A)))
      =O[𝓝[{A | Aᵀ = -A}] 0] fun A => ‖A‖ ^ 2 := by
  refine ((covDiff_exp Px Py).mono nhdsWithin_le_nhds).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with A hA
  rw [show Aᵀ = -A from hA, Matrix.mul_neg, ← sub_eq_add_neg]

/-! ## Propositions 32, 34, 38 and 39 -/

/-- **Proposition 32 (closed facts).** A gauge transformation takes `U_xy ↦ g_xU_xyg_y⁻¹`; the holonomy of a closed walk
at `x₀` turns by the gauge at its own vertex, `hol ↦ g_{x₀} hol g_{x₀}⁻¹`, so its trace is a fact (for every group of
invertible matrices over every commutative ring); the transport of an open walk from `x` to `y ≠ x` can be gauge-transformed
into every rotation, and only the constants are facts of it.

Recognition: Einstein's point coincidences and the gauge principle, with Wilson's closed loops. Uses P4,
Definition 24. -/
theorem prop_32_full {X G : Type*} [Group G] :
    (∀ (c : Connection X G) (g : X → G) (x y : X), (c.rename g).U x y = g x * c.U x y * (g y)⁻¹) ∧
    (∀ (c : Connection X G) (g : X → G) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) = x →
      hol (c.rename g) (x :: rest) = g x * hol c (x :: rest) * (g x)⁻¹) ∧
    (∀ {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) = x →
      IsFact (fun c : Connection X (Matrix n n R)ˣ =>
        ((hol c (x :: rest) : (Matrix n n R)ˣ) : Matrix n n R).trace)) ∧
    (∀ (c : Connection X G) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) ≠ x →
      ∀ V : G, ∃ g : X → G, hol (c.rename g) (x :: rest) = V) ∧
    (∀ {α : Type*} (φ : G → α) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) ≠ x →
      IsFact (fun c : Connection X G => φ (hol c (x :: rest))) → ∀ V W : G, φ V = φ W) := by
  obtain ⟨p1, p2, p3, p4⟩ := prop_32 (X := X) (G := G)
  exact ⟨p1, p2, fun x rest h => prop_32_trace x rest h, p3, p4⟩

/-- **Proposition 34 (spin one half).** `J_aJ_bJ_aJ_b = −1` (`a ≠ b`): the loop `f_∅ → f_b → f_{ab} → f_a → f_∅`
comes back with `−1`; `R_ab(ϑ) = e^{ϑJ_aJ_b/2} = cos(ϑ/2) + J_aJ_b sin(ϑ/2)`, `R_ab(ϑ) J(v) R_ab(ϑ)⁻¹ = J(O_ϑ v)`
for every `v` (`O_ϑ` the rotation of the plane `(a, b)` by `ϑ`), and `R_ab(2π) = −1` while `O_{2π} = 1`; with the square
root of the sign of a division `D`, `f_x = i^{[x ∈ D]} J_x` has `f_xf_y + f_yf_x = 2θ_D(x)δ_xy` and
`(f_xf_y)² = −θ_D(x)θ_D(y)` (`x ≠ y`): `−1` on the `C(k,2) + C(6−k,2)` planes within a side and `+1` on the
`k(6−k)` planes across (`k = |D|`); and these are the division's kept and moved rotations: a rotation is kept exactly when its
plane lies within one side.

Recognition: spin one half, four quarter turns around a plane come back with `−1`; a loop across the division is a
boost and never closes. Uses Props. 21, 33, Definition 14. -/
theorem prop_34_full {n : ℕ} :
    (∀ a b : Fin n, a ≠ b → SysExt.Jx (R := ℝ) a * SysExt.Jx b * SysExt.Jx a * SysExt.Jx b = -1) ∧
    (∀ a b : Fin n, a ≠ b →
      SysExt.Jx (R := ℝ) a (SysExt.Jx b (SysExt.Jx a (SysExt.Jx b (Pi.single (∅ : Finset (Fin n)) 1)))) =
        -Pi.single (∅ : Finset (Fin n)) (1 : ℝ)) ∧
    (∀ a b : Fin n, a ≠ b → ∀ θ : ℝ,
      NormedSpace.exp ((θ / 2) • LinearMap.toMatrixAlgEquiv' (SysExt.Jx (R := ℝ) a * SysExt.Jx b)) =
        LinearMap.toMatrixAlgEquiv' (SysExt.rotor a b θ) ∧
      SysExt.rotor a b θ = Real.cos (θ / 2) • 1 + Real.sin (θ / 2) • (SysExt.Jx a * SysExt.Jx b)) ∧
    (∀ a b : Fin n, a ≠ b → ∀ θ : ℝ, SysExt.rotor a b θ * SysExt.rotor a b (-θ) = 1 ∧
      ∀ v : Fin n → ℝ, SysExt.rotor a b θ * SysExt.Jv v * SysExt.rotor a b (-θ) =
        SysExt.Jv (SysExt.planeRot a b θ *ᵥ v)) ∧
    (∀ a b : Fin n, SysExt.rotor a b (2 * Real.pi) = -1 ∧ SysExt.planeRot a b (2 * Real.pi) = 1) ∧
    (∀ (D : Finset (Fin 6)) (x y : Fin 6),
      SysExt.halfStep D x * SysExt.halfStep D y + SysExt.halfStep D y * SysExt.halfStep D x =
        if x = y then (2 * thetaAt D x) • 1 else 0) ∧
    (∀ (D : Finset (Fin 6)) (x y : Fin 6), x ≠ y →
      (SysExt.halfStep D x * SysExt.halfStep D y) * (SysExt.halfStep D x * SysExt.halfStep D y) =
        (-(thetaAt D x * thetaAt D y)) • 1) ∧
    (∀ D : Finset (Fin 6),
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ (p.1 ∈ D ↔ p.2 ∈ D)).card =
        D.card.choose 2 + (6 - D.card).choose 2 ∧
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ¬(p.1 ∈ D ↔ p.2 ∈ D)).card =
        D.card * (6 - D.card)) ∧
    (∀ (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10), Kept D x ↔ ((plane x).1 ∈ D ↔ (plane x).2 ∈ D)) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := prop_34 (n := n)
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, kept_iff⟩

/-- **Proposition 38 (curvature).** The curvature `F_st(x) = hol(x; tsts) − 1` turns under a gauge transformation by
the gauge at its vertex, `F_st(x) ↦ g_xF_st(x)g_x⁻¹`; every closed walk of four steps is a square `tsts`; ten
squares pass through each vertex and there are forty in all, which with the sixteen vertices build the cells of `ℝP⁴`
(SI Prop. 116, `Comparison.System.prop_116`); for `U_{xy} = e^{a_{xy}}` near one, with `a = (a₁, …, a₄)` the rotations
of the four steps in order, `hol = exp(Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ]) + O(‖a‖³)` uniformly for small rotations, that is
`log hol = Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³)`.

Recognition: the curvature is the force, `F = dA + A ∧ A` when the vertices are many and the rotations small. Uses
Props. 25, 32, Definition 25. -/
theorem prop_38_full :
    (∀ {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (c : Connection (Fin 16) (Matrix n n R)ˣ)
      (g : Fin 16 → (Matrix n n R)ˣ) (x : Fin 16) (s t : Fin 5),
      curv (c.rename g) x s t = (g x : Matrix n n R) * curv c x s t * ((g x)⁻¹ : (Matrix n n R)ˣ)) ∧
    (∀ (x : Fin 16) (a b c d : Fin 5), a ≠ b → b ≠ c → c ≠ d → d ≠ a →
      transition d (transition c (transition b (transition a x))) = x → a = c ∧ b = d) ∧
    (∀ x : Fin 16, (Finset.image (fun p : Fin 5 × Fin 5 => square x p.1 p.2)
      (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2)).card = 10) ∧
    (Finset.image (fun p : Fin 16 × Fin 5 × Fin 5 => square p.1 p.2.1 p.2.2)
      (Finset.univ.filter fun p : Fin 16 × Fin 5 × Fin 5 => p.2.1 < p.2.2)).card = 40 ∧
    (∀ {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A],
      (fun a : A × A × A × A => NormedSpace.exp a.2.2.2 * NormedSpace.exp a.2.2.1 * NormedSpace.exp a.2.1 *
          NormedSpace.exp a.1 -
        NormedSpace.exp (a.1 + a.2.1 + a.2.2.1 + a.2.2.2 + (1 / 2 : ℝ) • Article.squareC a.1 a.2.1 a.2.2.1 a.2.2.2))
        =O[𝓝 0] fun a => ‖a‖ ^ 3) := by
  obtain ⟨p1, p2, p3, p4, -⟩ := prop_38
  exact ⟨p1, p2, p3, p4, fun {A} _ _ _ => bch_uniform (A := A)⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **Proposition 39 (kept and moved: the mass form).** `M_D(X, X) = ‖[X, P_D]‖² ≥ 0`, zero exactly when `X` is kept;
`M_D = 2` on every unit moved rotation `E_ab − E_ba` (`a ∈ D`, `b ∉ D`); between neighbouring vertices
`DP_D = U_{xy}P_D(y)U_{xy}⁻¹ − P_D(x) ↦ g_x(DP_D)g_x⁻¹`; near one, `U = e^A`,
`DP_D = (P_D(y) − P_D(x)) + (AP_D(y) + P_D(y)Aᵀ) + O(‖A‖²)`, which along the rotations `Aᵀ = −A` is
`(P_D(y) − P_D(x)) + [A, P_D(y)] + O(‖A‖²)`, and for `U = 1 + A` exactly `(P_D(y) − P_D(x)) + [A, P_D(y)] − AP_D(y)A`; with `q_D = 1 + (i − 1)P_D`,
`Dq_D = (i − 1)DP_D` and `‖Dq_D‖² = 2‖DP_D‖²`; along a rotation `X`, `‖Dq_D‖² = 2M_D(X, X)`.

Recognition: the kept rotations are massless gauge fields and the moved rotations massive (Englert, Brout, Higgs). Uses
Prop. 21, Definitions 15, 27. -/
theorem prop_39_full {n : ℕ} :
    (∀ (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ),
      massForm D X X = ∑ i, ∑ j, ((X * projD D - projD D * X) i j) ^ 2 ∧ 0 ≤ massForm D X X ∧
      (massForm D X X = 0 ↔ X * thetaD D = thetaD D * X)) ∧
    (∀ (D : Finset (Fin n)) (a b : Fin n), a ∈ D → b ∉ D → massForm D (unitTurn a b) (unitTurn a b) = 2) ∧
    (∀ U Px Py gx gy : Matrix (Fin n) (Fin n) ℝ, gyᵀ * gy = 1 →
      covDiff (gx * U * gyᵀ) (gx * Px * gxᵀ) (gy * Py * gyᵀ) = gx * covDiff U Px Py * gxᵀ) ∧
    (∀ Px Py : Matrix (Fin n) (Fin n) ℝ,
      (fun A : Matrix (Fin n) (Fin n) ℝ => covDiff (NormedSpace.exp A) Px Py - ((Py - Px) + (A * Py + Py * Aᵀ)))
        =O[𝓝 0] fun A => ‖A‖ ^ 2) ∧
    (∀ Px Py : Matrix (Fin n) (Fin n) ℝ,
      (fun A : Matrix (Fin n) (Fin n) ℝ => covDiff (NormedSpace.exp A) Px Py - ((Py - Px) + (A * Py - Py * A)))
        =O[𝓝[{A | Aᵀ = -A}] 0] fun A => ‖A‖ ^ 2) ∧
    (∀ A Py : Matrix (Fin n) (Fin n) ℝ, Aᵀ = -A → A * Py + Py * Aᵀ = A * Py - Py * A) ∧
    (∀ A Px Py : Matrix (Fin n) (Fin n) ℝ, Aᵀ = -A →
      covDiff (1 + A) Px Py = (Py - Px) + (A * Py - Py * A) - A * Py * A) ∧
    (∀ U Px Py : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 →
      covDiffC U (qHalf Px) (qHalf Py) = (Complex.I - 1) • toC (covDiff U Px Py)) ∧
    (∀ M : Matrix (Fin n) (Fin n) ℝ, frobSq ((Complex.I - 1) • toC M) = 2 * ∑ i, ∑ j, M i j ^ 2) ∧
    (∀ (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ),
      frobSq ((Complex.I - 1) • toC (X * projD D - projD D * X)) = 2 * massForm D X X) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := prop_39 (n := n)
  refine ⟨p1, p2, p3, covDiff_exp, covDiff_exp_turn, fun A Py hA => ?_, p4, p5, p6, p7⟩
  rw [hA, Matrix.mul_neg, sub_eq_add_neg]

end Comparison.System.Existence
