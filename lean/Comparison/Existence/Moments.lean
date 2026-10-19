module

public import Comparison.Colour.Visits

/-!
# Book VI. The visits of one excursion from `F(z, x, y)` (Proposition 29, B.29)

`excursionF z x y` is B.29's
`F(z, x, y) = z⁴x²y(1 + zy)/(16 − 8zy − 3z²xy − 3z³xy²)`, the unique solution of the first-step
equations of one excursion on its classes (`excursion_system`, `excursion_system_unique` in `Colour/Visits.lean`):
`z` marks a step, `x` an arrival at a vector state (`Q`), `y` an arrival at a symmetric state (`P`). At
`z = x = y = 1` the derivatives are the factorial moments:

* `EP_eq`: `∂_yF = E P = 10`; `EQ_eq`: `∂_xF = E Q = 5`; `El_eq`: `∂_zF = E ℓ = 16`.
* `FPP_eq`: `∂²_yF = E P(P − 1) = 174`; `FQQ_eq`: `∂²_xF = E Q(Q − 1) = 32`;
  `FPQ_eq`: `∂_x∂_yF = E PQ = 80`.
* `visit_moments`: **`Var P = 174 + 10 − 10² = 84`, `Var Q = 32 + 5 − 5² = 12`,
  `Cov(P, Q) = 80 − 10·5 = 30`**, and `Var P − Cov²/Var Q = 9`, `Var ℓ = Var(1 + P + Q) = 156`.

These were inputs of Prop. 71 (`Zero.lean`, `marks_centred`); here they are derived from `F`.
-/

@[expose] public section

namespace Comparison

open Filter Topology

/-- Two derivatives through an explicit derivative near the point. -/
theorem deriv_deriv_of {f g : ℝ → ℝ} {a c : ℝ} (hf : ∀ᶠ y in 𝓝 a, HasDerivAt f (g y) y)
    (hg : HasDerivAt g c a) : deriv (deriv f) a = c := by
  have h : deriv f =ᶠ[𝓝 a] g := hf.mono fun y hy => hy.deriv
  rw [h.deriv_eq, hg.deriv]

/-! ## Along the symmetric states: `F(1, 1, y) = G_P(y)` -/

theorem GP_hasDerivAt (y : ℝ) (hy : 16 - 11 * y - 3 * y ^ 2 ≠ 0) :
    HasDerivAt GP ((16 + 32 * y - 8 * y ^ 2) / (16 - 11 * y - 3 * y ^ 2) ^ 2) y := by
  have hN : HasDerivAt (fun y : ℝ => y * (1 + y)) (1 * (1 + y) + y * 1) y :=
    (hasDerivAt_id y).mul ((hasDerivAt_id y).const_add 1)
  have hD : HasDerivAt (fun y : ℝ => 16 - 11 * y - 3 * y ^ 2) (-(11 * 1) - 3 * (2 * y ^ 1 * 1)) y :=
    (((hasDerivAt_id y).const_mul 11).const_sub 16).sub ((hasDerivAt_pow 2 y).const_mul 3 |>.congr_deriv
      (by simp))
  have := hN.div hD hy
  refine this.congr_deriv ?_
  congr 1
  ring

theorem GP_second : HasDerivAt (fun y : ℝ => (16 + 32 * y - 8 * y ^ 2) / (16 - 11 * y - 3 * y ^ 2) ^ 2)
    174 1 := by
  have hN : HasDerivAt (fun y : ℝ => 16 + 32 * y - 8 * y ^ 2) 16 1 :=
    ((((hasDerivAt_id (1 : ℝ)).const_mul 32).const_add 16).sub
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 8)).congr_deriv (by norm_num)
  have h1 : HasDerivAt (fun y : ℝ => 16 - 11 * y - 3 * y ^ 2) (-17) 1 :=
    ((((hasDerivAt_id (1 : ℝ)).const_mul 11).const_sub 16).sub
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 3)).congr_deriv (by norm_num)
  have hD : HasDerivAt (fun y : ℝ => (16 - 11 * y - 3 * y ^ 2) ^ 2) (-68) 1 :=
    (h1.pow 2).congr_deriv (by norm_num)
  have := hN.div hD (by norm_num)
  refine this.congr_deriv ?_
  norm_num

/-- **`E P = ∂_yF(1, 1, 1) = 10`.** -/
theorem EP_eq : deriv (fun y => excursionF 1 1 y) 1 = 10 := by
  have h : (fun y => excursionF 1 1 y) = GP := funext fun y => (GP_eq y).symm
  rw [h, GP_deriv.deriv]

/-- **`E P(P − 1) = ∂²_yF(1, 1, 1) = 174`.** -/
theorem FPP_eq : deriv (deriv (fun y => excursionF 1 1 y)) 1 = 174 := by
  have h : (fun y => excursionF 1 1 y) = GP := funext fun y => (GP_eq y).symm
  rw [h]
  refine deriv_deriv_of ?_ GP_second
  have hc : ContinuousAt (fun y : ℝ => 16 - 11 * y - 3 * y ^ 2) 1 := by fun_prop
  filter_upwards [hc.eventually_ne (by norm_num : (16 - 11 * 1 - 3 * 1 ^ 2 : ℝ) ≠ 0)] with y hy
  exact GP_hasDerivAt y hy

/-! ## Along the vector states: `F(1, x, 1) = 2x²/(8 − 6x)` -/

theorem excursionF_x (x : ℝ) : excursionF 1 x 1 = 2 * x ^ 2 / (8 - 6 * x) := by
  simp only [excursionF, excursionDen]
  ring_nf

theorem GQ_hasDerivAt (x : ℝ) (hx : 8 - 6 * x ≠ 0) :
    HasDerivAt (fun x => excursionF 1 x 1) ((32 * x - 12 * x ^ 2) / (8 - 6 * x) ^ 2) x := by
  have hf : (fun x => excursionF 1 x 1) = fun x : ℝ => 2 * x ^ 2 / (8 - 6 * x) := funext excursionF_x
  rw [hf]
  have hN : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * x ^ 1 * 1)) x :=
    ((hasDerivAt_pow 2 x).const_mul 2).congr_deriv (by simp)
  have hD : HasDerivAt (fun x : ℝ => 8 - 6 * x) (-(6 * 1)) x :=
    ((hasDerivAt_id x).const_mul 6).const_sub 8
  refine (hN.div hD hx).congr_deriv ?_
  congr 1
  ring

theorem GQ_second : HasDerivAt (fun x : ℝ => (32 * x - 12 * x ^ 2) / (8 - 6 * x) ^ 2) 32 1 := by
  have hN : HasDerivAt (fun x : ℝ => 32 * x - 12 * x ^ 2) (32 * 1 - 12 * (2 * 1 ^ 1 * 1)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).const_mul 32).sub (((hasDerivAt_pow 2 (1 : ℝ)).const_mul 12).congr_deriv
      (by simp))
  have h1 : HasDerivAt (fun x : ℝ => 8 - 6 * x) (-6) 1 :=
    (((hasDerivAt_id (1 : ℝ)).const_mul 6).const_sub 8).congr_deriv (by norm_num)
  have hD : HasDerivAt (fun x : ℝ => (8 - 6 * x) ^ 2) (-24) 1 :=
    (h1.pow 2).congr_deriv (by norm_num)
  refine (hN.div hD (by norm_num)).congr_deriv ?_
  norm_num

/-- **`E Q = ∂_xF(1, 1, 1) = 5`.** -/
theorem EQ_eq : deriv (fun x => excursionF 1 x 1) 1 = 5 := by
  rw [(GQ_hasDerivAt 1 (by norm_num)).deriv]
  norm_num

/-- **`E Q(Q − 1) = ∂²_xF(1, 1, 1) = 32`.** -/
theorem FQQ_eq : deriv (deriv (fun x => excursionF 1 x 1)) 1 = 32 := by
  refine deriv_deriv_of ?_ GQ_second
  have hc : ContinuousAt (fun x : ℝ => 8 - 6 * x) 1 := by fun_prop
  filter_upwards [hc.eventually_ne (by norm_num : (8 - 6 * 1 : ℝ) ≠ 0)] with x hx
  exact GQ_hasDerivAt x hx

/-! ## The mixed moment -/

theorem Fy_at_one (x : ℝ) (hx : 8 - 6 * x ≠ 0) :
    HasDerivAt (fun y => excursionF 1 x y) (40 * x ^ 2 / (8 - 6 * x) ^ 2) 1 := by
  have hf : (fun y => excursionF 1 x y) =
      fun y : ℝ => x ^ 2 * (y * (1 + y)) / (16 - 8 * y - 3 * x * y - 3 * x * y ^ 2) := by
    funext y
    simp only [excursionF, excursionDen]
    ring_nf
  rw [hf]
  have hN : HasDerivAt (fun y : ℝ => x ^ 2 * (y * (1 + y))) (x ^ 2 * (1 * (1 + 1) + 1 * 1)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).mul ((hasDerivAt_id (1 : ℝ)).const_add 1)).const_mul (x ^ 2)
  have hD : HasDerivAt (fun y : ℝ => 16 - 8 * y - 3 * x * y - 3 * x * y ^ 2)
      (-(8 * 1) - 3 * x * 1 - 3 * x * (2 * 1 ^ 1 * 1)) 1 :=
    ((((hasDerivAt_id (1 : ℝ)).const_mul 8).const_sub 16).sub ((hasDerivAt_id (1 : ℝ)).const_mul
      (3 * x))).sub (((hasDerivAt_pow 2 (1 : ℝ)).const_mul (3 * x)).congr_deriv (by simp))
  have hD1 : (16 - 8 * 1 - 3 * x * 1 - 3 * x * 1 ^ 2 : ℝ) ≠ 0 := by
    intro h
    apply hx
    linarith
  refine (hN.div hD hD1).congr_deriv ?_
  field_simp
  ring

theorem Fy_second : HasDerivAt (fun x : ℝ => 40 * x ^ 2 / (8 - 6 * x) ^ 2) 80 1 := by
  have hN : HasDerivAt (fun x : ℝ => 40 * x ^ 2) (40 * (2 * 1 ^ 1 * 1)) 1 :=
    ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 40).congr_deriv (by simp)
  have h1 : HasDerivAt (fun x : ℝ => 8 - 6 * x) (-6) 1 :=
    (((hasDerivAt_id (1 : ℝ)).const_mul 6).const_sub 8).congr_deriv (by norm_num)
  have hD : HasDerivAt (fun x : ℝ => (8 - 6 * x) ^ 2) (-24) 1 :=
    (h1.pow 2).congr_deriv (by norm_num)
  refine (hN.div hD (by norm_num)).congr_deriv ?_
  norm_num

/-- **`E PQ = ∂_x∂_yF(1, 1, 1) = 80`.** -/
theorem FPQ_eq : deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 = 80 := by
  have hc : ContinuousAt (fun x : ℝ => 8 - 6 * x) 1 := by fun_prop
  have h : (fun x => deriv (fun y => excursionF 1 x y) 1) =ᶠ[𝓝 1]
      fun x : ℝ => 40 * x ^ 2 / (8 - 6 * x) ^ 2 := by
    filter_upwards [hc.eventually_ne (by norm_num : (8 - 6 * 1 : ℝ) ≠ 0)] with x hx
    exact (Fy_at_one x hx).deriv
  rw [h.deriv_eq, Fy_second.deriv]

/-! ## The length -/

/-- **`E ℓ = ∂_zF(1, 1, 1) = 16`.** -/
theorem El_eq : deriv (fun z => excursionF z 1 1) 1 = 16 := by
  have hf : (fun z => excursionF z 1 1) =
      fun z : ℝ => (z ^ 4 + z ^ 5) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) := by
    funext z
    simp only [excursionF, excursionDen]
    ring_nf
  rw [hf]
  have hN : HasDerivAt (fun z : ℝ => z ^ 4 + z ^ 5) 9 1 :=
    ((hasDerivAt_pow 4 (1 : ℝ)).add (hasDerivAt_pow 5 (1 : ℝ))).congr_deriv (by norm_num)
  have hD : HasDerivAt (fun z : ℝ => 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) (-23) 1 :=
    (((((hasDerivAt_id (1 : ℝ)).const_mul 8).const_sub 16).sub
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 3)).sub
        ((hasDerivAt_pow 3 (1 : ℝ)).const_mul 3)).congr_deriv (by norm_num)
  have hdiv : HasDerivAt (fun z : ℝ => (z ^ 4 + z ^ 5) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)) 16 1 :=
    (hN.div hD (by norm_num)).congr_deriv (by norm_num)
  rw [hdiv.deriv]

/-! ## The variances -/

/-- **`Var P = 84`, `Var Q = 12`, `Cov(P, Q) = 30`** from the factorial moments of `F`, with
`Var P − Cov²/Var Q = 9` and `Var ℓ = Var P + Var Q + 2 Cov = 156`. -/
theorem visit_moments :
    deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
        (deriv (fun y => excursionF 1 1 y) 1) ^ 2 = 84 ∧
      deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
        (deriv (fun x => excursionF 1 x 1) 1) ^ 2 = 12 ∧
      deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 -
        deriv (fun y => excursionF 1 1 y) 1 * deriv (fun x => excursionF 1 x 1) 1 = 30 ∧
      (84 : ℝ) - 30 ^ 2 / 12 = 9 ∧ (84 : ℝ) + 12 + 2 * 30 = 156 := by
  rw [FPP_eq, EP_eq, FQQ_eq, EQ_eq, FPQ_eq]
  norm_num

end Comparison

end
