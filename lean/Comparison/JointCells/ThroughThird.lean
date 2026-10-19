import Comparison.Law.Returns

/-!
# Comparisons compose through a third (Proposition 90), a result of the geometry, and what it fixes
# in a bound state of three world lines

Proposition 90 is not a postulate. Its proof uses two systems
only, and these are the only hypotheses of `through_third`: operators on different systems commute
(the composition `H_A ⊗ H_B` of P1: `ga_gb`, `ga_gc`, `gb_gc` are Kronecker products) and the five
directions of one system anticommute in pairs with square one (Proposition 4, from P3: `ga_clifford`
from `clifford`). Symmetrizing the two comparisons through the shared system leaves exactly the
comparison of the other two in the product of the frames; the part that depends on the order is a rotation
of the shared system (`commutator_sum`, `commutator_turns`, `product_through_third`): curvature where
it is recorded.

**Proposition 90.** Comparing a system `a` with `b` in the frame `A` and with `c` in the frame `B`,
`L_ab(A) = 1 + Σ_{s,t} A_st γ_s^{(a)} γ_t^{(b)}`, in either order, compares `b` with `c` in the frame
`AᵀB`, with weight one:
`½{L_ab(A), L_ac(B)} = L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2`.

* `through_third` (any ring with scalars, any frames `A`, `B`): the identity for any family `x_s` with
  `x_s x_u + x_u x_s = 2δ_su` commuting with families `y_t`, `z_v` that commute with each other; the
  shared leg is contracted, `Σ_s A_st B_sv = (AᵀB)_tv`, before any orthogonality is used.
* `prop90`: **Proposition 90 on three systems' four amplitudes**, `γ_s` on `a`, `b`, `c` as Kronecker
  products, for all complex `5 × 5` frames `A`, `B`; `prop90_order`: the two orders give the same
  third comparison.
* `triangle_flat`: for orthogonal frames the triangle `a → b → c → a` closes with the frame
  `A (AᵀB) Bᵀ = 1`: three comparisons made through a third are flat; `third_orientation`:
  `det(AᵀB) = det A det B`.

**What it fixes in a totally antisymmetric state of three world lines.** A pair that meets at the pattern `U` is compared in the
frame `θ_U` (`L_ab(θ_U)` is `6` on `e_U`, `comparison_frame_meeting`). Then:
* `third_pattern`: `θ_Uᵀ θ_V = θ_{U △ V}`: two pairs at `U` and `V` put the third pair at `U △ V`
  (Proposition 25's composition of two-spinor states, now as the frame of a comparison);
* `sign_triangle`: for every line `r`, `ε_r(U) ε_r(V) ε_r(U △ V) = 1`: a pair sign that is the
  pair's agreement on a line is fixed for the third pair by the other two, and the triangle's sign is
  `+1`, its phase zero; `no_negative_triangle`: three pair signs `−1` cannot occur;
  `two_at_plane`: two pairs at `F` put the third at the singlet;
* `gram_through_third`, `gram_through_third_pos`: the meeting matrix of three lines with overlap `g`
  and such signs is a sign gauge of the flat one, `det = (1 − g)²(1 + 2g) > 0` for `0 ≤ g < 1`, in
  particular at `g² = c = 8/15`: positivity is a consequence of Proposition 90, not an extra choice;
* `plane_colour_through_third`: **`θ_Fᵀθ_C = θ_{all five} = −1`**, the counterpart `{n}` of the singlet, of
  determinant `−1`: `F` and `C`, which no rotation transport joins (`no_rotation_plane_to_colour`),
  are joined through a third, by an orientation-reversing comparison at the singlet's counterpart `{n}`.
-/

open Comparison Matrix Kronecker
open Comparison.Law

namespace Comparison.JointCells.Third

/-! ## Proposition 90 in any algebra -/

section Abstract

variable {R : Type*} [CommRing R] {M : Type*} [Ring M] [Algebra R M]

/-- The comparison of two systems in the frame `A`: `1 + Σ_{s,t} A_st x_s y_t`. -/
def Lf (x y : Fin 5 → M) (A : Matrix (Fin 5) (Fin 5) R) : M :=
  1 + ∑ s, ∑ t, A s t • (x s * y t)

theorem sum_swap4 {N : Type*} [AddCommMonoid N] (h : Fin 5 → Fin 5 → Fin 5 → Fin 5 → N) :
    ∑ u, ∑ v, ∑ s, ∑ t, h u v s t = ∑ s, ∑ t, ∑ u, ∑ v, h u v s t := by
  calc ∑ u, ∑ v, ∑ s, ∑ t, h u v s t = ∑ u, ∑ s, ∑ v, ∑ t, h u v s t :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ u, ∑ s, ∑ t, ∑ v, h u v s t :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ s, ∑ u, ∑ t, ∑ v, h u v s t := Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ u, ∑ v, h u v s t := Finset.sum_congr rfl fun s _ => Finset.sum_comm

/-- One term: the shared leg anticommutes, the other two legs commute. -/
theorem term_anticomm (x y z : Fin 5 → M)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : R) else 0) • (1 : M))
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) (s t u v : Fin 5) :
    x s * y t * (x u * z v) + x u * z v * (x s * y t) =
      (if s = u then (2 : R) else 0) • (y t * z v) := by
  have e1 : x s * y t * (x u * z v) = (x s * x u) * (y t * z v) := by
    calc x s * y t * (x u * z v) = x s * (y t * x u) * z v := by simp only [mul_assoc]
      _ = x s * (x u * y t) * z v := by rw [hxy u t]
      _ = (x s * x u) * (y t * z v) := by simp only [mul_assoc]
  have e2 : x u * z v * (x s * y t) = (x u * x s) * (y t * z v) := by
    calc x u * z v * (x s * y t) = x u * (z v * x s) * y t := by simp only [mul_assoc]
      _ = x u * (x s * z v) * y t := by rw [hxz s v]
      _ = (x u * x s) * (z v * y t) := by simp only [mul_assoc]
      _ = (x u * x s) * (y t * z v) := by rw [hyz t v]
  rw [e1, e2, ← add_mul, hx s u, smul_mul_assoc, one_mul]

/-- **The anticommutator of the two comparisons contracts the shared leg:**
`{Σ A_st x_s y_t, Σ B_uv x_u z_v} = 2 Σ_{t,v} (AᵀB)_tv y_t z_v`. -/
theorem anticomm_sum (x y z : Fin 5 → M) (A B : Matrix (Fin 5) (Fin 5) R)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : R) else 0) • (1 : M))
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) :
    (∑ s, ∑ t, A s t • (x s * y t)) * (∑ u, ∑ v, B u v • (x u * z v)) +
      (∑ u, ∑ v, B u v • (x u * z v)) * (∑ s, ∑ t, A s t • (x s * y t)) =
      (2 : R) • ∑ t, ∑ v, (Aᵀ * B) t v • (y t * z v) := by
  have hXY : (∑ s, ∑ t, A s t • (x s * y t)) * (∑ u, ∑ v, B u v • (x u * z v)) =
      ∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • (x s * y t * (x u * z v)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_mul_smul_comm]
  have hYX0 : (∑ u, ∑ v, B u v • (x u * z v)) * (∑ s, ∑ t, A s t • (x s * y t)) =
      ∑ u, ∑ v, ∑ s, ∑ t, (A s t * B u v) • (x u * z v * (x s * y t)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, mul_comm (B u v) (A s t)]
  have hYX : (∑ u, ∑ v, B u v • (x u * z v)) * (∑ s, ∑ t, A s t • (x s * y t)) =
      ∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • (x u * z v * (x s * y t)) := by
    rw [hYX0]
    exact sum_swap4 (fun u v s t => (A s t * B u v) • (x u * z v * (x s * y t)))
  rw [hXY, hYX]
  have hsum : ∀ s t, (∑ u, ∑ v, (A s t * B u v) • (x s * y t * (x u * z v))) +
      (∑ u, ∑ v, (A s t * B u v) • (x u * z v * (x s * y t))) =
      ∑ v, (2 * (A s t * B s v)) • (y t * z v) := by
    intro s t
    rw [← Finset.sum_add_distrib]
    have hu : ∀ u, (∑ v, (A s t * B u v) • (x s * y t * (x u * z v))) +
        (∑ v, (A s t * B u v) • (x u * z v * (x s * y t))) =
        ∑ v, ((A s t * B u v) * (if s = u then (2 : R) else 0)) • (y t * z v) := by
      intro u
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← smul_add, term_anticomm x y z hx hxy hxz hyz, smul_smul]
    simp only [hu]
    rw [Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun v _ => ?_
      congr 1
      simp only [↓reduceIte]
      ring
    · intro u _ hus
      refine Finset.sum_eq_zero fun v _ => ?_
      have : ¬ s = u := fun h => hus h.symm
      simp [this]
    · simp
  have hL : (∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • (x s * y t * (x u * z v))) +
      (∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • (x u * z v * (x s * y t))) =
      ∑ s, ∑ t, ∑ v, (2 * (A s t * B s v)) • (y t * z v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => hsum s t
  rw [hL]
  have hR : (2 : R) • ∑ t, ∑ v, (Aᵀ * B) t v • (y t * z v) =
      ∑ t, ∑ v, ∑ s, (2 * (A s t * B s v)) • (y t * z v) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.transpose_apply, smul_smul]
  rw [hR]
  calc ∑ s, ∑ t, ∑ v, (2 * (A s t * B s v)) • (y t * z v)
      = ∑ t, ∑ s, ∑ v, (2 * (A s t * B s v)) • (y t * z v) := Finset.sum_comm
    _ = ∑ t, ∑ v, ∑ s, (2 * (A s t * B s v)) • (y t * z v) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm

/-- **Comparisons compose through a third** (Proposition 90), in any algebra:
`{L_ab(A), L_ac(B)} = 2 (L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2)`. -/
theorem through_third (x y z : Fin 5 → M) (A B : Matrix (Fin 5) (Fin 5) R)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : R) else 0) • (1 : M))
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) :
    Lf x y A * Lf x z B + Lf x z B * Lf x y A =
      (2 : R) • (Lf x y A + Lf x z B + Lf y z (Aᵀ * B) - 2) := by
  have h := anticomm_sum x y z A B hx hxy hxz hyz
  unfold Lf
  set X := ∑ s, ∑ t, A s t • (x s * y t)
  set Y := ∑ u, ∑ v, B u v • (x u * z v)
  set W := ∑ t, ∑ v, (Aᵀ * B) t v • (y t * z v)
  have e : (1 + X) * (1 + Y) + (1 + Y) * (1 + X) = (2 : R) • (1 : M) + (2 : R) • X +
      (2 : R) • Y + (X * Y + Y * X) := by
    simp only [two_smul, add_mul, mul_add, one_mul, mul_one]
    abel
  rw [e, h]
  have e2 : (2 : R) • ((1 + X) + (1 + Y) + (1 + W) - 2) =
      (2 : R) • (1 : M) + (2 : R) • X + (2 : R) • Y + (2 : R) • W := by
    have h2 : ((1 + X) + (1 + Y) + (1 + W) - 2 : M) = 1 + X + Y + W := by
      rw [show (2 : M) = 1 + 1 from one_add_one_eq_two.symm]
      abel
    rw [h2, smul_add, smul_add, smul_add]
  rw [e2]

/-- **The order-dependent part:** `[Σ A_st x_s y_t, Σ B_uv x_u z_v] = Σ (A_st B_uv)(x_s x_u − x_u x_s) y_t z_v`,
using only that operators on different systems commute. -/
theorem commutator_sum (x y z : Fin 5 → M) (A B : Matrix (Fin 5) (Fin 5) R)
    (hxy : ∀ s t, x s * y t = y t * x s) (hxz : ∀ s v, x s * z v = z v * x s)
    (hyz : ∀ t v, y t * z v = z v * y t) :
    (∑ s, ∑ t, A s t • (x s * y t)) * (∑ u, ∑ v, B u v • (x u * z v)) -
      (∑ u, ∑ v, B u v • (x u * z v)) * (∑ s, ∑ t, A s t • (x s * y t)) =
      ∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • ((x s * x u - x u * x s) * (y t * z v)) := by
  have hXY : (∑ s, ∑ t, A s t • (x s * y t)) * (∑ u, ∑ v, B u v • (x u * z v)) =
      ∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • (x s * y t * (x u * z v)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_mul_smul_comm]
  have hYX0 : (∑ u, ∑ v, B u v • (x u * z v)) * (∑ s, ∑ t, A s t • (x s * y t)) =
      ∑ u, ∑ v, ∑ s, ∑ t, (A s t * B u v) • (x u * z v * (x s * y t)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, mul_comm (B u v) (A s t)]
  rw [hXY, hYX0, sum_swap4 (fun u v s t => (A s t * B u v) • (x u * z v * (x s * y t))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← smul_sub]
  congr 1
  have e1 : x s * y t * (x u * z v) = (x s * x u) * (y t * z v) := by
    calc x s * y t * (x u * z v) = x s * (y t * x u) * z v := by simp only [mul_assoc]
      _ = x s * (x u * y t) * z v := by rw [hxy u t]
      _ = (x s * x u) * (y t * z v) := by simp only [mul_assoc]
  have e2 : x u * z v * (x s * y t) = (x u * x s) * (y t * z v) := by
    calc x u * z v * (x s * y t) = x u * (z v * x s) * y t := by simp only [mul_assoc]
      _ = x u * (x s * z v) * y t := by rw [hxz s v]
      _ = (x u * x s) * (z v * y t) := by simp only [mul_assoc]
      _ = (x u * x s) * (y t * z v) := by rw [hyz t v]
  rw [e1, e2, ← sub_mul]

/-- **The order-dependent part is a rotation of the shared system:** with Proposition 4, `x_s x_u − x_u x_s`
is `0` for `s = u` and `2 x_s x_u` (the rotation of the plane `(s u)`) for `s ≠ u`. -/
theorem commutator_turns (x : Fin 5 → M)
    (hx : ∀ s u, x s * x u + x u * x s = (if s = u then (2 : R) else 0) • (1 : M)) (s u : Fin 5) :
    x s * x u - x u * x s = if s = u then 0 else (2 : R) • (x s * x u) := by
  split_ifs with h
  · subst h; rw [sub_self]
  · have h0 := hx s u
    simp only [h, ↓reduceIte, zero_smul] at h0
    have h1 : x u * x s = -(x s * x u) := eq_neg_of_add_eq_zero_right h0
    rw [h1, sub_neg_eq_add, two_smul]

end Abstract

/-! ## Proposition 90 on three systems -/

/-- Three systems: the amplitudes of `a`, `b`, `c`. -/
abbrev Three := (Four × Four) × Four

/-- The line `s` on the system `a`, `b` or `c`. -/
def ga (s : Fin 5) : Matrix Three Three ℂ := (γ s ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ (1 : Matrix Four Four ℂ)
def gb (s : Fin 5) : Matrix Three Three ℂ := ((1 : Matrix Four Four ℂ) ⊗ₖ γ s) ⊗ₖ (1 : Matrix Four Four ℂ)
def gc (s : Fin 5) : Matrix Three Three ℂ := ((1 : Matrix Four Four ℂ) ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ γ s

theorem ga_clifford (s u : Fin 5) :
    ga s * ga u + ga u * ga s = (if s = u then (2 : ℂ) else 0) • (1 : Matrix Three Three ℂ) := by
  simp only [ga, ← mul_kronecker_mul, Matrix.mul_one, ← add_kronecker, clifford s u, smul_kronecker,
    one_kronecker_one]

theorem ga_gb (s t : Fin 5) : ga s * gb t = gb t * ga s := by
  simp only [ga, gb, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem ga_gc (s v : Fin 5) : ga s * gc v = gc v * ga s := by
  simp only [ga, gc, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem gb_gc (t v : Fin 5) : gb t * gc v = gc v * gb t := by
  simp only [gb, gc, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The comparisons of the pairs `(a, b)`, `(a, c)`, `(b, c)` in frames. -/
def Lab (A : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Three Three ℂ := Lf ga gb A
def Lac (A : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Three Three ℂ := Lf ga gc A
def Lbc (A : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Three Three ℂ := Lf gb gc A

/-- **Proposition 90 on three systems:** `½{L_ab(A), L_ac(B)} = L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2`, for
all frames `A`, `B`. -/
theorem prop90 (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    Lab A * Lac B + Lac B * Lab A = (2 : ℂ) • (Lab A + Lac B + Lbc (Aᵀ * B) - 2) :=
  through_third ga gb gc A B ga_clifford ga_gb ga_gc gb_gc

/-- **The order of the two comparisons does not change the third:** the anticommutator is symmetric,
and the third comparison `L_bc(AᵀB)` is read off it alone. -/
theorem prop90_order (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    Lbc (Aᵀ * B) = (1 / 2 : ℂ) • (Lab A * Lac B + Lac B * Lab A) - Lab A - Lac B + 2 := by
  rw [prop90, smul_smul]
  norm_num
  abel

/-- The order-dependent part of the product on three systems: rotations of the shared system `a`. -/
noncomputable def turnPart (A B : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Three Three ℂ :=
  ∑ s, ∑ t, ∑ u, ∑ v, (A s t * B u v) • ((ga s * ga u - ga u * ga s) * (gb t * gc v))

/-- **The product of the two comparisons:** `L_ab(A) L_ac(B) = L_ab(A) + L_ac(B) + L_bc(AᵀB) − 2 + ½T`,
`T` the rotation of the shared system; in the other order `− ½T`. The order-free part is the third
comparison; the order is recorded only in the rotation. -/
theorem product_through_third (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    Lab A * Lac B = Lab A + Lac B + Lbc (Aᵀ * B) - 2 + (1 / 2 : ℂ) • turnPart A B ∧
      Lac B * Lab A = Lab A + Lac B + Lbc (Aᵀ * B) - 2 - (1 / 2 : ℂ) • turnPart A B := by
  have hs := prop90 A B
  have hc : Lab A * Lac B - Lac B * Lab A = turnPart A B := by
    unfold Lab Lac Lf turnPart
    have e : (1 + ∑ s, ∑ t, A s t • (ga s * gb t)) * (1 + ∑ u, ∑ v, B u v • (ga u * gc v)) -
        (1 + ∑ u, ∑ v, B u v • (ga u * gc v)) * (1 + ∑ s, ∑ t, A s t • (ga s * gb t)) =
        (∑ s, ∑ t, A s t • (ga s * gb t)) * (∑ u, ∑ v, B u v • (ga u * gc v)) -
        (∑ u, ∑ v, B u v • (ga u * gc v)) * (∑ s, ∑ t, A s t • (ga s * gb t)) := by
      noncomm_ring
    rw [e]
    exact commutator_sum ga gb gc A B ga_gb ga_gc gb_gc
  have half : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  constructor
  · have e1 : Lab A * Lac B = (1 / 2 : ℂ) • (Lab A * Lac B + Lac B * Lab A) +
        (1 / 2 : ℂ) • (Lab A * Lac B - Lac B * Lab A) := by
      rw [← smul_add]
      have e2 : Lab A * Lac B + Lac B * Lab A + (Lab A * Lac B - Lac B * Lab A) =
          (2 : ℂ) • (Lab A * Lac B) := by
        rw [two_smul]; abel
      rw [e2, smul_smul, half, one_smul]
    rw [e1, hs, hc, smul_smul, half, one_smul]
  · have e1 : Lac B * Lab A = (1 / 2 : ℂ) • (Lab A * Lac B + Lac B * Lab A) -
        (1 / 2 : ℂ) • (Lab A * Lac B - Lac B * Lab A) := by
      rw [← smul_sub]
      have e2 : Lab A * Lac B + Lac B * Lab A - (Lab A * Lac B - Lac B * Lab A) =
          (2 : ℂ) • (Lac B * Lab A) := by
        rw [two_smul]; abel
      rw [e2, smul_smul, half, one_smul]
    rw [e1, hs, hc, smul_smul, half, one_smul]

/-- **The rotation part carries only rotations of the shared system:** its terms with `s = u` vanish and those
with `s ≠ u` are `2 (γ_sγ_u)^{(a)} γ_t^{(b)} γ_v^{(c)}`. -/
theorem turnPart_turns (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    turnPart A B = ∑ s, ∑ t, ∑ u, ∑ v,
      (A s t * B u v) • ((if s = u then (0 : Matrix Three Three ℂ) else (2 : ℂ) • (ga s * ga u)) *
        (gb t * gc v)) := by
  unfold turnPart
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [commutator_turns ga ga_clifford s u]

/-- With the identity frame, `L_ab(1)` is the comparison `1 + Σ_s γ_s^{(a)} γ_s^{(b)}` (Definition 10). -/
theorem Lab_one : Lab 1 = 1 + ∑ s, ga s * gb s := by
  unfold Lab Lf
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Ne.symm hts]
  · simp

/-! ## What the composition fixes -/

/-- **The triangle closes flat:** for orthogonal frames the frame round `a → b → c → a` is
`A (AᵀB) Bᵀ = 1`. -/
theorem triangle_flat {K : Type*} [CommRing K] (A B : Matrix (Fin 5) (Fin 5) K)
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) : A * (Aᵀ * B) * Bᵀ = 1 := by
  have hA' : A * Aᵀ = 1 := mul_eq_one_comm.mp hA
  have hB' : B * Bᵀ = 1 := mul_eq_one_comm.mp hB
  calc A * (Aᵀ * B) * Bᵀ = (A * Aᵀ) * (B * Bᵀ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA', hB', Matrix.mul_one]

/-- The orientation of the third comparison is the product of the other two. -/
theorem third_orientation {K : Type*} [CommRing K] (A B : Matrix (Fin 5) (Fin 5) K) :
    (Aᵀ * B).det = A.det * B.det := by
  rw [det_mul, det_transpose]

/-- **A pair meeting at `U` is compared in the frame `θ_U`:** `L_ab(θ_U)` is `1 + Σ_s ε_s(U) γ_s ⊗ γ_s`,
which is `6` on the two-spinor state `e_U` (two systems, `agreement`). -/
theorem comparison_frame_meeting (k : Fin 16) :
    ((1 : Matrix Two Two ℂ) + ∑ s, (if s ∈ disagreeSet k then -1 else 1 : ℂ) • (γ s ⊗ₖ γ s)) *ᵥ
        rel k = (6 : ℂ) • rel k := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, agreement, smul_smul]
  have h : ∀ s : Fin 5, ((if s ∈ disagreeSet k then -1 else 1 : ℂ) *
      (if s ∈ disagreeSet k then -1 else 1 : ℂ)) = 1 := by
    intro s; split_ifs <;> norm_num
  simp only [h, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply]
  norm_num
  ring

/-- **Two pairs at `U` and `V` put the third pair at `U △ V`:** `θ_Uᵀ θ_V = θ_{U △ V}`. -/
theorem third_pattern {K : Type*} [CommRing K] (U V : Finset (Fin 5)) :
    (thetaP (R := K) U)ᵀ * thetaP V = thetaP (symmDiff U V) := by
  rw [thetaP, thetaP, thetaP, diagonal_transpose, diagonal_mul_diagonal]
  congr 1
  funext s
  by_cases hU : s ∈ U <;> by_cases hV : s ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- The agreement sign of a pair on a line. -/
def agr (U : Finset (Fin 5)) (r : Fin 5) : ℤ := if r ∈ U then -1 else 1

/-- **The triangle of signs is `+1`:** for every line `r`, `ε_r(U) ε_r(V) ε_r(U △ V) = 1`. -/
theorem sign_triangle (U V : Finset (Fin 5)) (r : Fin 5) :
    agr U r * agr V r * agr (symmDiff U V) r = 1 := by
  unfold agr
  by_cases hU : r ∈ U <;> by_cases hV : r ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- **The third sign is fixed by the other two:** `ε_r(U △ V) = ε_r(U) ε_r(V)`. -/
theorem third_sign (U V : Finset (Fin 5)) (r : Fin 5) :
    agr (symmDiff U V) r = agr U r * agr V r := by
  unfold agr
  by_cases hU : r ∈ U <;> by_cases hV : r ∈ V <;> simp [hU, hV, Finset.mem_symmDiff]

/-- **No negative triangle through a third:** three pair signs `−1` on one line cannot occur when the
third pair is composed from the other two. -/
theorem no_negative_triangle (U V : Finset (Fin 5)) (r : Fin 5) :
    ¬ (agr U r = -1 ∧ agr V r = -1 ∧ agr (symmDiff U V) r = -1) := by
  rintro ⟨h1, h2, h3⟩
  have := sign_triangle U V r
  rw [h1, h2, h3] at this
  norm_num at this

/-- **Two pairs at the plane put the third pair at the singlet.** -/
theorem two_at_plane : symmDiff ({0, 1} : Finset (Fin 5)) {0, 1} = ∅ := symmDiff_self _

/-- **The meeting matrix of three lines composed through a third** is a sign gauge of the flat one:
with signs `σ₁₂, σ₁₃` and `σ₂₃ = σ₁₂σ₁₃`, `det = (1 − g)²(1 + 2g)`. -/
theorem gram_through_third (g σ₁₂ σ₁₃ : ℝ) (h₁₂ : σ₁₂ * σ₁₂ = 1) (h₁₃ : σ₁₃ * σ₁₃ = 1) :
    (!![1, σ₁₂ * g, σ₁₃ * g; σ₁₂ * g, 1, σ₁₂ * σ₁₃ * g; σ₁₃ * g, σ₁₂ * σ₁₃ * g, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det = (1 - g) ^ 2 * (1 + 2 * g) := by
  rw [Matrix.det_fin_three]
  simp
  linear_combination ((-g ^ 2 + 2 * g ^ 3) * σ₁₂ ^ 2 - g ^ 2) * h₁₃ + (-2 * g ^ 2 + 2 * g ^ 3) * h₁₂

/-- **Positivity follows:** for `0 ≤ g < 1` the determinant is positive; at `g² = 8/15` in particular. -/
theorem gram_through_third_pos (g : ℝ) (h0 : 0 ≤ g) (h1 : g < 1) : 0 < (1 - g) ^ 2 * (1 + 2 * g) := by
  have ha : 0 < (1 - g) ^ 2 := by
    have : 0 < 1 - g := by linarith
    positivity
  have hb : 0 < 1 + 2 * g := by linarith
  exact mul_pos ha hb

theorem c_overlap_lt_one : Real.sqrt (8 / 15) < 1 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- The plane `F = {h, k}` and its colour counterpart `C`. -/
def planeF : Finset (Fin 5) := {0, 1}
def colourC : Finset (Fin 5) := {2, 3, 4}

/-- **`F` and `C` through a third:** `θ_Fᵀ θ_C = θ_{all five} = −1`, the counterpart `{n}` of the singlet, of
determinant `−1`: a system compared with `b` at `F` and with `c` at `C` compares `b` with `c` at the singlet's counterpart
`{n}`, an orientation-reversing comparison of type `1|5`. -/
theorem plane_colour_through_third :
    (thetaP (R := ℂ) planeF)ᵀ * thetaP colourC = thetaP Finset.univ ∧
      thetaP (R := ℂ) Finset.univ = -1 ∧ (thetaP (R := ℂ) Finset.univ).det = -1 ∧
      symmDiff planeF colourC = Finset.univ := by
  have hsd : symmDiff planeF colourC = Finset.univ := by decide
  refine ⟨by rw [third_pattern, hsd], ?_, ?_, hsd⟩
  · rw [thetaP]
    ext i j
    simp [diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [full_cycle]
    simp
    norm_num

/-- The comparison at the singlet's counterpart `{n}`: `L_bc(−1) = 1 − Σ_s γ_s^{(b)} γ_s^{(c)}`, through `a` at `F` and
`C`. -/
theorem plane_colour_comparison :
    Lbc ((thetaP (R := ℂ) planeF)ᵀ * thetaP colourC) = 1 - ∑ s, gb s * gc s := by
  rw [plane_colour_through_third.1, plane_colour_through_third.2.1]
  unfold Lbc Lf
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Matrix.neg_apply, Ne.symm hts]
  · simp

/-- **On two systems the comparison at the singlet's counterpart `{n}` is `2|T_k| − 4`:** `(1 − Σ_s γ_s ⊗ γ_s) e_k =
(2|T_k| − 4) e_k`, so it is `−4` on the singlet, `0` on the ten symmetric states and `4` on the five vector
states: joined through a third at `F` and `C`, the other two systems' comparison vanishes on the symmetric states. -/
theorem twin_comparison_on_rel (k : Fin 16) :
    ((1 : Matrix Two Two ℂ) - ∑ s, γ s ⊗ₖ γ s) *ᵥ rel k =
      ((2 : ℂ) * (disagreeSet k).card - 4) • rel k := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp only [agreement]
  rw [← Finset.sum_smul, sum_sign]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Comparison.JointCells.Third

#print axioms Comparison.JointCells.Third.sum_swap4
#print axioms Comparison.JointCells.Third.term_anticomm
#print axioms Comparison.JointCells.Third.anticomm_sum
#print axioms Comparison.JointCells.Third.through_third
#print axioms Comparison.JointCells.Third.commutator_sum
#print axioms Comparison.JointCells.Third.commutator_turns
#print axioms Comparison.JointCells.Third.ga_clifford
#print axioms Comparison.JointCells.Third.ga_gb
#print axioms Comparison.JointCells.Third.ga_gc
#print axioms Comparison.JointCells.Third.gb_gc
#print axioms Comparison.JointCells.Third.prop90
#print axioms Comparison.JointCells.Third.prop90_order
#print axioms Comparison.JointCells.Third.product_through_third
#print axioms Comparison.JointCells.Third.turnPart_turns
#print axioms Comparison.JointCells.Third.Lab_one
#print axioms Comparison.JointCells.Third.triangle_flat
#print axioms Comparison.JointCells.Third.third_orientation
#print axioms Comparison.JointCells.Third.comparison_frame_meeting
#print axioms Comparison.JointCells.Third.third_pattern
#print axioms Comparison.JointCells.Third.sign_triangle
#print axioms Comparison.JointCells.Third.third_sign
#print axioms Comparison.JointCells.Third.no_negative_triangle
#print axioms Comparison.JointCells.Third.two_at_plane
#print axioms Comparison.JointCells.Third.gram_through_third
#print axioms Comparison.JointCells.Third.gram_through_third_pos
#print axioms Comparison.JointCells.Third.c_overlap_lt_one
#print axioms Comparison.JointCells.Third.plane_colour_through_third
#print axioms Comparison.JointCells.Third.plane_colour_comparison
#print axioms Comparison.JointCells.Third.twin_comparison_on_rel
