import Comparison.Article.Holonomy

/-!
# The proof system, the existence layer: the closed walk to the second order, uniformly (Proposition 38)

For four rotations `a = (a₁, a₂, a₃, a₄)` in a complete normed real
algebra, `e^{a₄}e^{a₃}e^{a₂}e^{a₁} = exp(Σ aᵢ + ½ Σ_{i>j} [aᵢ, aⱼ]) + O(‖a‖³)` uniformly near `0` (`bch_uniform`).
The proof carries second-order jets at `0` of functions on a normed space (`MJet`): `f v = c₀ + c₁ v + c₂ v + O(‖v‖³)`
with `c₁ = O(‖v‖)` and `c₂ = O(‖v‖²)`; jets multiply (`MJet.mul`), the exponential of `S + D` has the jet
`1 + S + (D + S²/2)` (`mjet_exp`), and the two sides have one jet (`Splits.bch_second_order`'s identity).

Also `exp y = 1 + y + O(‖y‖²)` (`exp_first_order`), used for the transport of Proposition 39.
-/

namespace Comparison.System.Existence

open Asymptotics Filter NormedSpace Topology

section MJet

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {V : Type*} [NormedAddCommGroup V]

theorem eventually_norm_le_one : ∀ᶠ v : V in 𝓝 0, ‖v‖ ≤ 1 := by
  have : Metric.closedBall (0 : V) 1 ∈ 𝓝 (0 : V) := Metric.closedBall_mem_nhds 0 one_pos
  filter_upwards [this] with v hv
  simpa [Metric.mem_closedBall, dist_zero_right] using hv

theorem pow_isBigO_pow {m k : ℕ} (hkm : k ≤ m) : (fun v : V => ‖v‖ ^ m) =O[𝓝 0] fun v => ‖v‖ ^ k := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_norm_le_one] with v hv
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg v) hv hkm

theorem pow_isBigO_one (m : ℕ) : (fun v : V => ‖v‖ ^ m) =O[𝓝 0] fun _ => (1 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_norm_le_one] with v hv
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm, abs_one, one_mul]
  exact pow_le_one₀ (norm_nonneg v) hv

theorem norm_isBigO_one : (fun v : V => ‖v‖) =O[𝓝 0] fun _ => (1 : ℝ) :=
  (pow_isBigO_one (V := V) 1).congr_left fun v => pow_one ‖v‖

/-- **A second-order jet at `0`:** `f v = c₀ + c₁ v + c₂ v + O(‖v‖³)`, `c₁ = O(‖v‖)`, `c₂ = O(‖v‖²)`. -/
structure MJet (f : V → A) (c₀ : A) (c₁ c₂ : V → A) : Prop where
  rem : (fun v => f v - (c₀ + c₁ v + c₂ v)) =O[𝓝 0] fun v => ‖v‖ ^ 3
  one : c₁ =O[𝓝 0] fun v => ‖v‖
  two : c₂ =O[𝓝 0] fun v => ‖v‖ ^ 2

theorem MJet.poly_bounded {f : V → A} {c₀ : A} {c₁ c₂ : V → A} (hf : MJet f c₀ c₁ c₂) :
    (fun v => c₀ + c₁ v + c₂ v) =O[𝓝 0] fun _ => (1 : ℝ) :=
  ((isBigO_const_one ℝ c₀ (𝓝 (0 : V))).add (hf.one.trans norm_isBigO_one)).add
    (hf.two.trans (pow_isBigO_one 2))

theorem MJet.bounded {f : V → A} {c₀ : A} {c₁ c₂ : V → A} (hf : MJet f c₀ c₁ c₂) :
    f =O[𝓝 0] fun _ => (1 : ℝ) := by
  have h := (hf.rem.trans (pow_isBigO_one 3)).add hf.poly_bounded
  refine h.congr_left fun v => ?_
  abel

/-- **Jets multiply.** -/
theorem MJet.mul {f g : V → A} {f₀ g₀ : A} {f₁ f₂ g₁ g₂ : V → A} (hf : MJet f f₀ f₁ f₂) (hg : MJet g g₀ g₁ g₂) :
    MJet (fun v => f v * g v) (f₀ * g₀) (fun v => f₀ * g₁ v + f₁ v * g₀)
      (fun v => f₀ * g₂ v + f₁ v * g₁ v + f₂ v * g₀) where
  rem := by
    have e : (fun v => f v * g v - (f₀ * g₀ + (f₀ * g₁ v + f₁ v * g₀) + (f₀ * g₂ v + f₁ v * g₁ v + f₂ v * g₀))) =
        fun v => (f₁ v * g₂ v + f₂ v * g₁ v + f₂ v * g₂ v) + (f₀ + f₁ v + f₂ v) * (g v - (g₀ + g₁ v + g₂ v)) +
          (f v - (f₀ + f₁ v + f₂ v)) * g v := by
      funext v
      noncomm_ring
    rw [e]
    have a1 : (fun v => f₁ v * g₂ v) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      (hf.one.mul hg.two).congr_right fun v => by ring
    have a2 : (fun v => f₂ v * g₁ v) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      (hf.two.mul hg.one).congr_right fun v => by ring
    have a3 : (fun v => f₂ v * g₂ v) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      ((hf.two.mul hg.two).congr_right fun v => by ring).trans (pow_isBigO_pow (m := 4) (k := 3) (by norm_num))
    have a4 : (fun v => (f₀ + f₁ v + f₂ v) * (g v - (g₀ + g₁ v + g₂ v))) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      (hf.poly_bounded.mul hg.rem).congr_right fun v => one_mul _
    have a5 : (fun v => (f v - (f₀ + f₁ v + f₂ v)) * g v) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      (hf.rem.mul hg.bounded).congr_right fun v => mul_one _
    exact (((a1.add a2).add a3).add a4).add a5
  one := by
    have b1 : (fun v => f₀ * g₁ v) =O[𝓝 0] fun v => ‖v‖ :=
      ((isBigO_const_one ℝ f₀ (𝓝 (0 : V))).mul hg.one).congr_right fun v => one_mul _
    have b2 : (fun v => f₁ v * g₀) =O[𝓝 0] fun v => ‖v‖ :=
      (hf.one.mul (isBigO_const_one ℝ g₀ (𝓝 (0 : V)))).congr_right fun v => mul_one _
    exact b1.add b2
  two := by
    have b1 : (fun v => f₀ * g₂ v) =O[𝓝 0] fun v => ‖v‖ ^ 2 :=
      ((isBigO_const_one ℝ f₀ (𝓝 (0 : V))).mul hg.two).congr_right fun v => one_mul _
    have b2 : (fun v => f₁ v * g₁ v) =O[𝓝 0] fun v => ‖v‖ ^ 2 :=
      (hf.one.mul hg.one).congr_right fun v => by ring
    have b3 : (fun v => f₂ v * g₀) =O[𝓝 0] fun v => ‖v‖ ^ 2 :=
      (hf.two.mul (isBigO_const_one ℝ g₀ (𝓝 (0 : V)))).congr_right fun v => mul_one _
    exact (b1.add b2).add b3

/-- Two functions with one jet differ by `O(‖v‖³)`. -/
theorem MJet.sub_isBigO {f g : V → A} {c₀ d₀ : A} {c₁ c₂ d₁ d₂ : V → A} (hf : MJet f c₀ c₁ c₂)
    (hg : MJet g d₀ d₁ d₂) (h0 : c₀ = d₀) (h12 : ∀ v, c₁ v + c₂ v = d₁ v + d₂ v) :
    (fun v => f v - g v) =O[𝓝 0] fun v => ‖v‖ ^ 3 := by
  refine (hf.rem.sub hg.rem).congr_left fun v => ?_
  have e1 : c₀ + c₁ v + c₂ v = d₀ + d₁ v + d₂ v := by rw [add_assoc, add_assoc, h0, h12 v]
  rw [e1]
  abel

/-- **The exponential of `S + D`**, `S = O(‖v‖)`, `D = O(‖v‖²)`: the jet `1 + S + (D + S²/2)`. -/
theorem mjet_exp {S D : V → A} (hS : S =O[𝓝 0] fun v => ‖v‖) (hD : D =O[𝓝 0] fun v => ‖v‖ ^ 2) :
    MJet (fun v => exp (S v + D v)) 1 S (fun v => D v + (1 / 2 : ℝ) • (S v * S v)) where
  rem := by
    have hD1 : D =O[𝓝 0] fun v => ‖v‖ :=
      (hD.trans (pow_isBigO_pow (V := V) (m := 2) (k := 1) (by norm_num))).congr_right fun v => pow_one _
    have hX : (fun v => S v + D v) =O[𝓝 0] fun v => ‖v‖ := hS.add hD1
    have hXt : Tendsto (fun v => S v + D v) (𝓝 0) (𝓝 0) := hX.trans_tendsto tendsto_norm_zero
    have hR := (Article.exp_second_order (A := A)).comp_tendsto hXt
    have hX3 : (fun v => ‖S v + D v‖ ^ 3) =O[𝓝 0] fun v => ‖v‖ ^ 3 := (isBigO_norm_left.mpr hX).pow 3
    have hR' : (fun v => exp (S v + D v) - (1 + (S v + D v) + (1 / 2 : ℝ) • ((S v + D v) * (S v + D v)))) =O[𝓝 0]
        fun v => ‖v‖ ^ 3 := hR.trans hX3
    have c1 : (fun v => S v * D v) =O[𝓝 0] fun v => ‖v‖ ^ 3 := (hS.mul hD).congr_right fun v => by ring
    have c2 : (fun v => D v * S v) =O[𝓝 0] fun v => ‖v‖ ^ 3 := (hD.mul hS).congr_right fun v => by ring
    have c3 : (fun v => D v * D v) =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      ((hD.mul hD).congr_right fun v => by ring).trans (pow_isBigO_pow (m := 4) (k := 3) (by norm_num))
    have hpoly : (fun v => (1 / 2 : ℝ) • (S v * D v) + (1 / 2 : ℝ) • (D v * S v) + (1 / 2 : ℝ) • (D v * D v))
        =O[𝓝 0] fun v => ‖v‖ ^ 3 :=
      ((c1.const_smul_left (1 / 2 : ℝ)).add (c2.const_smul_left (1 / 2 : ℝ))).add (c3.const_smul_left (1 / 2 : ℝ))
    refine (hR'.add hpoly).congr_left fun v => ?_
    simp only [add_mul, mul_add, smul_add]
    abel
  one := hS
  two := hD.add (((hS.mul hS).congr_right fun v => by ring).const_smul_left (1 / 2 : ℝ))

end MJet

section Square

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem coord1_isBigO : (fun a : A × A × A × A => a.1) =O[𝓝 0] fun a => ‖a‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_norm, one_mul]
    exact norm_fst_le a)

theorem coord2_isBigO : (fun a : A × A × A × A => a.2.1) =O[𝓝 0] fun a => ‖a‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_norm, one_mul]
    exact (norm_fst_le a.2).trans (norm_snd_le a))

theorem coord3_isBigO : (fun a : A × A × A × A => a.2.2.1) =O[𝓝 0] fun a => ‖a‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_norm, one_mul]
    exact (norm_fst_le a.2.2).trans ((norm_snd_le a.2).trans (norm_snd_le a)))

theorem coord4_isBigO : (fun a : A × A × A × A => a.2.2.2) =O[𝓝 0] fun a => ‖a‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_norm, one_mul]
    exact (norm_snd_le a.2.2).trans ((norm_snd_le a.2).trans (norm_snd_le a)))

theorem comm_isBigO {p q : A × A × A × A → A} (hp : p =O[𝓝 0] fun a => ‖a‖) (hq : q =O[𝓝 0] fun a => ‖a‖) :
    (fun a => q a * p a - p a * q a) =O[𝓝 0] fun a => ‖a‖ ^ 2 :=
  ((hq.mul hp).congr_right fun a => (sq ‖a‖).symm).sub ((hp.mul hq).congr_right fun a => (sq ‖a‖).symm)

theorem mjet_exp_coord {p : A × A × A × A → A} (hp : p =O[𝓝 0] fun a => ‖a‖) :
    MJet (fun a => exp (p a)) 1 p (fun a => (0 : A) + (1 / 2 : ℝ) • (p a * p a)) := by
  have h := mjet_exp (S := p) (D := fun _ => (0 : A)) hp (isBigO_zero _ _)
  simpa using h

/-- **Proposition 38's line, uniformly:** `e^{a₄}e^{a₃}e^{a₂}e^{a₁} = exp(Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ]) + O(‖a‖³)` for
small rotations `a = (a₁, …, a₄)`, that is `log hol = Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³)`. -/
theorem bch_uniform :
    (fun a : A × A × A × A => exp a.2.2.2 * exp a.2.2.1 * exp a.2.1 * exp a.1 -
      exp (a.1 + a.2.1 + a.2.2.1 + a.2.2.2 + (1 / 2 : ℝ) • Article.squareC a.1 a.2.1 a.2.2.1 a.2.2.2)) =O[𝓝 0]
      fun a => ‖a‖ ^ 3 := by
  have j4 := mjet_exp_coord (coord4_isBigO (A := A))
  have j3 := mjet_exp_coord (coord3_isBigO (A := A))
  have j2 := mjet_exp_coord (coord2_isBigO (A := A))
  have j1 := mjet_exp_coord (coord1_isBigO (A := A))
  have j4321 := ((j4.mul j3).mul j2).mul j1
  have hS : (fun a : A × A × A × A => a.1 + a.2.1 + a.2.2.1 + a.2.2.2) =O[𝓝 0] fun a => ‖a‖ :=
    ((coord1_isBigO.add coord2_isBigO).add coord3_isBigO).add coord4_isBigO
  have hC : (fun a : A × A × A × A => Article.squareC a.1 a.2.1 a.2.2.1 a.2.2.2) =O[𝓝 0] fun a => ‖a‖ ^ 2 := by
    have c1 := coord1_isBigO (A := A)
    have c2 := coord2_isBigO (A := A)
    have c3 := coord3_isBigO (A := A)
    have c4 := coord4_isBigO (A := A)
    have h := (((((comm_isBigO c1 c2).add (comm_isBigO c1 c3)).add (comm_isBigO c2 c3)).add
      (comm_isBigO c1 c4)).add (comm_isBigO c2 c4)).add (comm_isBigO c3 c4)
    exact h.congr_left fun a => by simp only [Article.squareC]
  have jZ := mjet_exp hS (hC.const_smul_left (1 / 2 : ℝ))
  have key := j4321.sub_isBigO jZ (by simp) fun a => by
    simp only [Pi.smul_apply, Article.squareC, one_mul, mul_one, zero_add, add_mul, mul_add, smul_add, smul_sub,
      mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  refine key.congr_left fun a => ?_
  rfl

end Square

section FirstOrder

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- `exp y = 1 + y + O(‖y‖²)`. -/
theorem exp_first_order : (fun y : A => exp y - (1 + y)) =O[𝓝 0] fun y : A => ‖y‖ ^ 2 := by
  have h := (exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := A)).isBigO_sub_partialSum_pow 2
  refine h.congr_left fun y => ?_
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, expSeries_apply_eq]
  simp

end FirstOrder

end Comparison.System.Existence
