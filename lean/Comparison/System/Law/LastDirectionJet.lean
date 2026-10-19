import Comparison.System.Postulates
import Comparison.Existence.LastDirectionSplit
import Comparison.WholePicture.Curvature

/-!
# The proof system, the law: the curvature at the last-step direction from the first jet of the connection

The connection of the ten rotations split at the last-step direction `h`,
`𝒜_μ = ¼ω_μ^{ab}γ_aγ_b + (1/2ℓ)e_μ^aγ_hγ_a` (`a, b ≠ h`, `ω` antisymmetric), with its first jet at a point (the
derivatives `∂_μω_ν`, `∂_μe_ν`). Here:

* `comm_two_two`: in any ring, `[AB, CD] = A{B,C}D − AC{B,D} + {A,C}DB − C{A,D}B`;
* `gamma_comm`: `[γ_aγ_b, γ_cγ_d] = 2δ_bcγ_aγ_d − 2δ_bdγ_aγ_c + 2δ_acγ_dγ_b − 2δ_adγ_cγ_b`;
* `comm_sum_sum`: the commutator of two combinations is the double sum of the commutators;
* `bracket_six_six`, `bracket_four_four`, `bracket_six_four`: the brackets of the six with the six, the four with the
  four, the six with the four;
* `curvature_jet`: **`𝓕_μν = ∂_μ𝒜_ν − ∂_ν𝒜_μ + [𝒜_μ, 𝒜_ν] = ¼(R^{ab}_μν − (e∧e)^{ab}_μν/ℓ²)γ_aγ_b +
  (1/2ℓ)T^a_μνγ_hγ_a`** with `R = dω + ω∧ω` and `T = de + ω∧e`.
-/

open Matrix Complex Comparison Finset

namespace Comparison.System

namespace Law

/-- In any ring, `[AB, CD] = A{B,C}D − AC{B,D} + {A,C}DB − C{A,D}B`. -/
theorem comm_two_two {R : Type*} [Ring R] (A B C D : R) :
    A * B * (C * D) - C * D * (A * B) =
      A * (B * C + C * B) * D - A * C * (B * D + D * B) + (A * C + C * A) * D * B -
        C * (A * D + D * A) * B := by
  noncomm_ring

/-- **The bracket of two rotations:** `[γ_aγ_b, γ_cγ_d] = 2δ_bcγ_aγ_d − 2δ_bdγ_aγ_c + 2δ_acγ_dγ_b − 2δ_adγ_cγ_b`. -/
theorem gamma_comm (a b c d : Fin 5) :
    γ a * γ b * (γ c * γ d) - γ c * γ d * (γ a * γ b) =
      (if b = c then (2 : ℂ) else 0) • (γ a * γ d) - (if b = d then (2 : ℂ) else 0) • (γ a * γ c) +
        (if a = c then (2 : ℂ) else 0) • (γ d * γ b) -
          (if a = d then (2 : ℂ) else 0) • (γ c * γ b) := by
  rw [comm_two_two, clifford b c, clifford b d, clifford a c, clifford a d]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **The commutator of two combinations** is the double sum of the commutators. -/
theorem comm_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℂ) (y : κ → ℂ)
    (P : ι → Matrix Four Four ℂ) (Q : κ → Matrix Four Four ℂ) :
    (∑ i ∈ s, x i • P i) * (∑ j ∈ t, y j • Q j) - (∑ j ∈ t, y j • Q j) * (∑ i ∈ s, x i • P i) =
      ∑ i ∈ s, ∑ j ∈ t, (x i * y j) • (P i * Q j - Q j * P i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Finset.sum_comm (s := t)]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_sub, mul_comm (y j) (x i)]

/-- Contracting a Kronecker delta in a sum over a set that contains the index. -/
theorem sum_delta_left {β : Type*} [AddCommMonoid β] (S : Finset (Fin 5)) (b : Fin 5) (hb : b ∈ S)
    (f : Fin 5 → β) : ∑ c ∈ S, (if b = c then f c else 0) = f b := by
  rw [Finset.sum_ite_eq, if_pos hb]

theorem sum_delta_right {β : Type*} [AddCommMonoid β] (S : Finset (Fin 5)) (b : Fin 5) (hb : b ∈ S)
    (f : Fin 5 → β) : ∑ c ∈ S, (if c = b then f c else 0) = f b := by
  rw [Finset.sum_ite_eq', if_pos hb]

/-! ## The six and the four -/

/-- `Σ_{a,b∈S} X_ab γ_aγ_b`. -/
noncomputable def six (S : Finset (Fin 5)) (X : Fin 5 → Fin 5 → ℂ) : Matrix Four Four ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, X a b • (γ a * γ b)

/-- `Σ_{a∈S} x_a γ_hγ_a`. -/
noncomputable def four (h : Fin 5) (S : Finset (Fin 5)) (x : Fin 5 → ℂ) : Matrix Four Four ℂ :=
  ∑ a ∈ S, x a • (γ h * γ a)

theorem six_eq_product (S : Finset (Fin 5)) (X : Fin 5 → Fin 5 → ℂ) :
    six S X = ∑ p ∈ S ×ˢ S, X p.1 p.2 • (γ p.1 * γ p.2) := by
  rw [six, Finset.sum_product]

theorem contract_bc (S : Finset (Fin 5)) (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Matrix Four Four ℂ) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, (if b = c then f a b c d else 0) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ d ∈ S, f a b b d := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => sum_delta_left S b hb (fun c => f a b c d)

theorem contract_bd (S : Finset (Fin 5)) (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Matrix Four Four ℂ) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, (if b = d then f a b c d else 0) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, f a b c b :=
  Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
    Finset.sum_congr rfl fun c _ => sum_delta_left S b hb (fun d => f a b c d)

theorem contract_ac (S : Finset (Fin 5)) (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Matrix Four Four ℂ) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, (if a = c then f a b c d else 0) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ d ∈ S, f a b a d := by
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => sum_delta_left S a ha (fun c => f a b c d)

theorem contract_ad (S : Finset (Fin 5)) (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Matrix Four Four ℂ) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, (if a = d then f a b c d else 0) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, f a b c a :=
  Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => sum_delta_left S a ha (fun d => f a b c d)

theorem smul_ite_smul (k : ℂ) (P : Prop) [Decidable P] (M : Matrix Four Four ℂ) :
    k • ((if P then (2 : ℂ) else 0) • M) = if P then (2 * k) • M else 0 := by
  split_ifs <;> simp [smul_smul, mul_comm]

/-- Three sums reversed. -/
theorem sum3_rev {β : Type*} [AddCommMonoid β] (S : Finset (Fin 5)) (F : Fin 5 → Fin 5 → Fin 5 → β) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, F a b c = ∑ c ∈ S, ∑ b ∈ S, ∑ a ∈ S, F a b c :=
  calc ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, F a b c = ∑ b ∈ S, ∑ a ∈ S, ∑ c ∈ S, F a b c := Finset.sum_comm
    _ = ∑ b ∈ S, ∑ c ∈ S, ∑ a ∈ S, F a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ c ∈ S, ∑ b ∈ S, ∑ a ∈ S, F a b c := Finset.sum_comm

/-- The inner two of three sums exchanged. -/
theorem sum3_inner {β : Type*} [AddCommMonoid β] (S : Finset (Fin 5)) (F : Fin 5 → Fin 5 → Fin 5 → β) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, F a b c = ∑ a ∈ S, ∑ c ∈ S, ∑ b ∈ S, F a b c :=
  Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- **The bracket of the six with the six:** for antisymmetric `X, Y`,
`[Σ X_ab γ_aγ_b, Σ Y_cd γ_cγ_d] = 4 Σ (XY − YX)_ab γ_aγ_b`. -/
theorem bracket_six_six (S : Finset (Fin 5)) (X Y : Fin 5 → Fin 5 → ℂ)
    (hY : ∀ a b, Y b a = -Y a b) :
    six S X * six S Y - six S Y * six S X =
      (4 : ℂ) • six S (fun a b => ∑ c ∈ S, (X a c * Y c b - Y a c * X c b)) := by
  rw [six_eq_product S X, six_eq_product S Y, comm_sum_sum]
  simp only [Finset.sum_product, gamma_comm, smul_sub, smul_add, smul_ite_smul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [contract_bc S (fun a b c d => (2 * (X a b * Y c d)) • (γ a * γ d)),
    contract_bd S (fun a b c d => (2 * (X a b * Y c d)) • (γ a * γ c)),
    contract_ac S (fun a b c d => (2 * (X a b * Y c d)) • (γ d * γ b)),
    contract_ad S (fun a b c d => (2 * (X a b * Y c d)) • (γ c * γ b))]
  -- every sum in the form `Σ_x Σ_y Σ_c (coefficient) • (γ_xγ_y)`
  have t1 : ∑ a ∈ S, ∑ b ∈ S, ∑ d ∈ S, (2 * (X a b * Y b d)) • (γ a * γ d) =
      ∑ x ∈ S, ∑ y ∈ S, ∑ c ∈ S, (2 * (X x c * Y c y)) • (γ x * γ y) :=
    sum3_inner S _
  have t2 : ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (2 * (X a b * Y c b)) • (γ a * γ c) =
      ∑ x ∈ S, ∑ y ∈ S, ∑ c ∈ S, (-(2 * (X x c * Y c y))) • (γ x * γ y) := by
    rw [sum3_inner S]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hY c y]
    congr 1
    ring
  have t3 : ∑ a ∈ S, ∑ b ∈ S, ∑ d ∈ S, (2 * (X a b * Y a d)) • (γ d * γ b) =
      ∑ x ∈ S, ∑ y ∈ S, ∑ c ∈ S, (-(2 * (Y x c * X c y))) • (γ x * γ y) := by
    rw [sum3_rev S]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hY x c]
    congr 1
    ring
  have t4 : ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (2 * (X a b * Y c a)) • (γ c * γ b) =
      ∑ x ∈ S, ∑ y ∈ S, ∑ c ∈ S, (2 * (Y x c * X c y)) • (γ x * γ y) := by
    rw [sum3_rev S]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ring
  have hR : (4 : ℂ) • six S (fun a b => ∑ c ∈ S, X a c * Y c b - ∑ c ∈ S, Y a c * X c b) =
      ∑ x ∈ S, ∑ y ∈ S, ∑ c ∈ S, (4 * (X x c * Y c y - Y x c * X c y)) • (γ x * γ y) := by
    simp only [six, ← Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [t1, t2, t3, t4, hR]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  ring

/-- **The bracket of the four with the four:** `[Σ x_aγ_hγ_a, Σ y_bγ_hγ_b] = −Σ (x_ay_b − y_ax_b)γ_aγ_b`
(the indices off the last-step direction): `[ℝ⁴, ℝ⁴] ⊆ so(4)`. -/
theorem bracket_four_four (h : Fin 5) (x y : Fin 5 → ℂ) :
    four h (univ.erase h) x * four h (univ.erase h) y - four h (univ.erase h) y * four h (univ.erase h) x =
      -six (univ.erase h) (fun a b => x a * y b - y a * x b) := by
  set S := univ.erase h with hS
  rw [four, four, comm_sum_sum]
  have hterm : ∀ a ∈ S, ∀ b ∈ S, (x a * y b) • (γ h * γ a * (γ h * γ b) - γ h * γ b * (γ h * γ a)) =
      (x a * y b) • (γ b * γ a) - (x a * y b) • (γ a * γ b) := by
    intro a ha b hb
    have ha' : a ≠ h := Finset.ne_of_mem_erase ha
    have hb' : b ≠ h := Finset.ne_of_mem_erase hb
    rw [gamma_comm, if_neg ha', if_neg (Ne.symm hb'), if_pos rfl, γ_mul_self, ← clifford a b]
    module
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hterm a ha b hb]
  simp only [Finset.sum_sub_distrib]
  have hswap : ∑ a ∈ S, ∑ b ∈ S, (x a * y b) • (γ b * γ a) =
      ∑ a ∈ S, ∑ b ∈ S, (y a * x b) • (γ a * γ b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  rw [hswap, six]
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- **The bracket of the six with the four:** for antisymmetric `X`,
`[Σ X_abγ_aγ_b, Σ y_cγ_hγ_c] = 4 Σ (Xy)_aγ_hγ_a` (the indices off the last-step direction). -/
theorem bracket_six_four (h : Fin 5) (X : Fin 5 → Fin 5 → ℂ) (hX : ∀ a b, X b a = -X a b)
    (y : Fin 5 → ℂ) :
    six (univ.erase h) X * four h (univ.erase h) y - four h (univ.erase h) y * six (univ.erase h) X =
      (4 : ℂ) • four h (univ.erase h) (fun a => ∑ b ∈ univ.erase h, X a b * y b) := by
  set S := univ.erase h with hS
  rw [six_eq_product S X, four, comm_sum_sum]
  simp only [Finset.sum_product]
  have hterm : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      (X a b * y c) • (γ a * γ b * (γ h * γ c) - γ h * γ c * (γ a * γ b)) =
        (if b = c then (2 * (X a b * y c)) • (γ h * γ a) else 0) -
          (if a = c then (2 * (X a b * y c)) • (γ h * γ b) else 0) := by
    intro a ha b hb c _
    have ha' : a ≠ h := Finset.ne_of_mem_erase ha
    have hb' : b ≠ h := Finset.ne_of_mem_erase hb
    rw [gamma_comm, if_neg hb', if_neg ha', γ_anticomm ha']
    split_ifs <;> module
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    Finset.sum_congr rfl fun c hc => hterm a ha b hb c hc]
  simp only [Finset.sum_sub_distrib]
  have c1 : ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if b = c then (2 * (X a b * y c)) • (γ h * γ a) else 0) =
      ∑ a ∈ S, ∑ b ∈ S, (2 * (X a b * y b)) • (γ h * γ a) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      sum_delta_left S b hb (fun c => (2 * (X a b * y c)) • (γ h * γ a))
  have c2 : ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if a = c then (2 * (X a b * y c)) • (γ h * γ b) else 0) =
      ∑ a ∈ S, ∑ b ∈ S, (-(2 * (X a b * y b))) • (γ h * γ a) := by
    have e1 : ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S,
        (if a = c then (2 * (X a b * y c)) • (γ h * γ b) else 0) =
        ∑ a ∈ S, ∑ b ∈ S, (2 * (X a b * y a)) • (γ h * γ b) :=
      Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ =>
        sum_delta_left S a ha (fun c => (2 * (X a b * y c)) • (γ h * γ b))
    rw [e1]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX a b]
    congr 1
    ring
  rw [c1, c2, four]
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← sub_smul]
  congr 1
  ring

/-! ## The curvature of the connection at the last-step direction -/

/-- The commutator of two combinations of two pieces. -/
theorem comm_lin (α β : ℂ) (P Q P' Q' : Matrix Four Four ℂ) :
    (α • P + β • Q) * (α • P' + β • Q') - (α • P' + β • Q') * (α • P + β • Q) =
      (α * α) • (P * P' - P' * P) + (α * β) • (P * Q' - Q' * P) -
        (α * β) • (P' * Q - Q * P') + (β * β) • (Q * Q' - Q' * Q) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

theorem six_combo (S : Finset (Fin 5)) (A B C D : Fin 5 → Fin 5 → ℂ) (k : ℂ) :
    six S (fun a b => A a b - B a b + C a b - k * D a b) =
      six S A - six S B + six S C - k • six S D := by
  simp only [six, sub_smul, add_smul, mul_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum]

theorem four_combo (h : Fin 5) (S : Finset (Fin 5)) (A B C D : Fin 5 → ℂ) :
    four h S (fun a => A a - B a + (C a - D a)) = four h S A - four h S B + (four h S C - four h S D) := by
  simp only [four, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **The connection of the ten split at the last-step direction:** `𝒜 = ¼Σ_{a,b≠h} ω^{ab}γ_aγ_b + (1/2ℓ)Σ_{a≠h} e^aγ_hγ_a`. -/
noncomputable def lastDirectionConn (h : Fin 5) (ℓ : ℂ) (ω : Fin 5 → Fin 5 → ℂ) (e : Fin 5 → ℂ) :
    Matrix Four Four ℂ :=
  (1 / 4 : ℂ) • six (univ.erase h) ω + (1 / (2 * ℓ)) • four h (univ.erase h) e

/-- **The curvature of the connection from its first jet:** with `𝒜_μ = lastDirectionConn ω_μ e_μ`, the jet
`∂_μ𝒜_ν = lastDirectionConn (∂_μω_ν) (∂_μe_ν)` and `ω_μ`, `ω_ν` antisymmetric,
`𝓕_μν = ∂_μ𝒜_ν − ∂_ν𝒜_μ + [𝒜_μ, 𝒜_ν] = ¼ Σ (R^{ab}_μν − (e∧e)^{ab}_μν/ℓ²) γ_aγ_b + (1/2ℓ) Σ T^a_μν γ_hγ_a` with
`R^{ab} = ∂_μω_ν^{ab} − ∂_νω_μ^{ab} + Σ_c(ω_μ^{ac}ω_ν^{cb} − ω_ν^{ac}ω_μ^{cb})`, `(e∧e)^{ab} = e_μ^ae_ν^b − e_ν^ae_μ^b`
and `T^a = ∂_μe_ν^a − ∂_νe_μ^a + Σ_b(ω_μ^{ab}e_ν^b − ω_ν^{ab}e_μ^b)`. -/
theorem curvature_jet (h : Fin 5) (ℓ : ℂ) (hℓ : ℓ ≠ 0)
    (ωμ ων dωμν dωνμ : Fin 5 → Fin 5 → ℂ) (eμ eν deμν deνμ : Fin 5 → ℂ)
    (hμ : ∀ a b, ωμ b a = -ωμ a b) (hν : ∀ a b, ων b a = -ων a b) :
    lastDirectionConn h ℓ dωμν deμν - lastDirectionConn h ℓ dωνμ deνμ +
        (lastDirectionConn h ℓ ωμ eμ * lastDirectionConn h ℓ ων eν - lastDirectionConn h ℓ ων eν * lastDirectionConn h ℓ ωμ eμ) =
      (1 / 4 : ℂ) • six (univ.erase h) (fun a b =>
          dωμν a b - dωνμ a b + ∑ c ∈ univ.erase h, (ωμ a c * ων c b - ων a c * ωμ c b) -
            (1 / ℓ ^ 2) * (eμ a * eν b - eν a * eμ b)) +
        (1 / (2 * ℓ)) • four h (univ.erase h) (fun a =>
          deμν a - deνμ a + (∑ b ∈ univ.erase h, ωμ a b * eν b - ∑ b ∈ univ.erase h, ων a b * eμ b)) := by
  have hc : lastDirectionConn h ℓ ωμ eμ * lastDirectionConn h ℓ ων eν - lastDirectionConn h ℓ ων eν * lastDirectionConn h ℓ ωμ eμ =
      ((1 / 4 : ℂ) * (1 / 4)) • ((4 : ℂ) • six (univ.erase h)
          (fun a b => ∑ c ∈ univ.erase h, (ωμ a c * ων c b - ων a c * ωμ c b))) +
        ((1 / 4 : ℂ) * (1 / (2 * ℓ))) •
          ((4 : ℂ) • four h (univ.erase h) (fun a => ∑ b ∈ univ.erase h, ωμ a b * eν b)) -
        ((1 / 4 : ℂ) * (1 / (2 * ℓ))) •
          ((4 : ℂ) • four h (univ.erase h) (fun a => ∑ b ∈ univ.erase h, ων a b * eμ b)) +
        ((1 / (2 * ℓ)) * (1 / (2 * ℓ))) •
          (-six (univ.erase h) (fun a b => eμ a * eν b - eν a * eμ b)) := by
    rw [lastDirectionConn, lastDirectionConn, comm_lin, bracket_six_six (univ.erase h) ωμ ων hν,
      bracket_six_four h ωμ hμ eν, bracket_six_four h ων hν eμ, bracket_four_four h eμ eν]
  rw [hc, six_combo, four_combo, lastDirectionConn, lastDirectionConn]
  have h2 : (2 : ℂ) * ℓ ≠ 0 := mul_ne_zero two_ne_zero hℓ
  have e1 : ((1 / (2 * ℓ)) * (1 / (2 * ℓ)) : ℂ) = (1 / 4) * (1 / ℓ ^ 2) := by
    field_simp
    ring
  rw [e1]
  module

/-- The last-step direction curvature of `Existence/LastDirectionSplit.lean` is `¼Σ F_abγ_aγ_b + ½Σ T_aγ_hγ_a`. -/
theorem lastDirectionCurv_eq (h : Fin 5) (F : Fin 5 → Fin 5 → ℂ) (T : Fin 5 → ℂ) :
    lastDirectionCurv h F T = (1 / 4 : ℂ) • six (univ.erase h) F + (1 / 2 : ℂ) • four h (univ.erase h) T := by
  simp only [lastDirectionCurv, six, four, Finset.sum_product, Finset.smul_sum, mul_smul]

/-- **The curvature is the last-step direction curvature** `𝓕 = lastDirectionCurv h (R − e∧e/ℓ²) (T/ℓ)`. -/
theorem curvature_jet_lastDirectionCurv (h : Fin 5) (ℓ : ℂ) (hℓ : ℓ ≠ 0)
    (ωμ ων dωμν dωνμ : Fin 5 → Fin 5 → ℂ) (eμ eν deμν deνμ : Fin 5 → ℂ)
    (hμ : ∀ a b, ωμ b a = -ωμ a b) (hν : ∀ a b, ων b a = -ων a b) :
    lastDirectionConn h ℓ dωμν deμν - lastDirectionConn h ℓ dωνμ deνμ +
        (lastDirectionConn h ℓ ωμ eμ * lastDirectionConn h ℓ ων eν - lastDirectionConn h ℓ ων eν * lastDirectionConn h ℓ ωμ eμ) =
      lastDirectionCurv h (fun a b =>
          dωμν a b - dωνμ a b + ∑ c ∈ univ.erase h, (ωμ a c * ων c b - ων a c * ωμ c b) -
            (1 / ℓ ^ 2) * (eμ a * eν b - eν a * eμ b))
        (fun a => (1 / ℓ) * (deμν a - deνμ a +
          (∑ b ∈ univ.erase h, ωμ a b * eν b - ∑ b ∈ univ.erase h, ων a b * eμ b))) := by
  rw [curvature_jet h ℓ hℓ ωμ ων dωμν dωνμ eμ eν deμν deνμ hμ hν, lastDirectionCurv_eq]
  congr 1
  rw [four, four, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

/-! ## The trace against the last-step direction, with the form indices -/

/-- **The bilinear trace against the last-step direction:** `tr(γ_h 𝓕 𝓕′) = ¼ Σ ε_{habcd} F_ab F′_cd`. -/
theorem trace_lastDirection_curv_bilin (h : Fin 5) (F F' : Fin 5 → Fin 5 → ℂ) (T T' : Fin 5 → ℂ) :
    (γ h * lastDirectionCurv h F T * lastDirectionCurv h F' T').trace =
      (1 / 4 : ℂ) * ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
        (lc5 h p.1 p.2 q.1 q.2 : ℂ) * F p.1 p.2 * F' q.1 q.2 := by
  simp only [lastDirectionCurv, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  rw [trace_bilin, trace_bilin, trace_bilin, trace_bilin]
  have e1 : ∀ a b c d : Fin 5, (γ h * (γ a * γ b) * (γ c * γ d)).trace = 4 * (lc5 h a b c d : ℂ) :=
    fun a b c d => by rw [← trace_five]; congr 1; noncomm_ring
  have r1 : ∀ a b c : Fin 5, lc5 h a b h c = 0 := fun a b c => (lc5_lastDirection_repeat h a b c).1
  have r2 : ∀ a b c : Fin 5, lc5 h h a b c = 0 := fun a b c => (lc5_lastDirection_repeat h a b c).2.1
  simp only [e1, r1, r2, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The four-form pairing at the last-step direction:**
`X ∧ Y = Σ_{μνρσ} ε^{μνρσ} Σ_{(a,b),(c,d)} ε_{habcd} X^{ab}_{μν} Y^{cd}_{ρσ}`. -/
noncomputable def lastDirectionWedge (h : Fin 5) (X Y : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) : ℂ :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (WholePicture.eps4 μ ν ρ σ : ℂ) *
    ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
      (lc5 h p.1 p.2 q.1 q.2 : ℂ) * X μ ν p.1 p.2 * Y ρ σ q.1 q.2

/-- **`tr(γ_h 𝓕 ∧ 𝓕) = ¼ 𝓕 ∧ 𝓕`** with the form indices: for every curvature two-form
`𝓕_μν = ¼F^{ab}_μνγ_aγ_b + ½T^a_μνγ_hγ_a`. -/
theorem trace_four_form (h : Fin 5) (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ)
    (T : Fin 4 → Fin 4 → Fin 5 → ℂ) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (WholePicture.eps4 μ ν ρ σ : ℂ) *
        (γ h * lastDirectionCurv h (F μ ν) (T μ ν) * lastDirectionCurv h (F ρ σ) (T ρ σ)).trace =
      (1 / 4 : ℂ) * lastDirectionWedge h F F := by
  simp only [trace_lastDirection_curv_bilin, lastDirectionWedge, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem eps4_pair_swap : ∀ μ ν ρ σ : Fin 4,
    WholePicture.eps4 μ ν ρ σ = WholePicture.eps4 ρ σ μ ν := by decide

theorem sum4_swap {β : Type*} [AddCommMonoid β] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → β) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ = ∑ μ, ∑ ν, ∑ ρ, ∑ σ, f ρ σ μ ν :=
  calc ∑ μ, ∑ ν, ∑ ρ, ∑ σ, f μ ν ρ σ = ∑ μ, ∑ ρ, ∑ ν, ∑ σ, f μ ν ρ σ :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ ρ, ∑ μ, ∑ ν, ∑ σ, f μ ν ρ σ := Finset.sum_comm
    _ = ∑ ρ, ∑ μ, ∑ σ, ∑ ν, f μ ν ρ σ :=
        Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ ρ, ∑ σ, ∑ μ, ∑ ν, f μ ν ρ σ := Finset.sum_congr rfl fun ρ _ => Finset.sum_comm

theorem lastDirectionWedge_symm (h : Fin 5) (X Y : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) :
    lastDirectionWedge h X Y = lastDirectionWedge h Y X := by
  have inner : ∀ μ ν ρ σ : Fin 4,
      (∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
        (lc5 h p.1 p.2 q.1 q.2 : ℂ) * X μ ν p.1 p.2 * Y ρ σ q.1 q.2) =
      ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
        (lc5 h p.1 p.2 q.1 q.2 : ℂ) * Y ρ σ p.1 p.2 * X μ ν q.1 q.2 := by
    intro μ ν ρ σ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [lc5_pair_swap h q.1 q.2 p.1 p.2]
    ring
  unfold lastDirectionWedge
  simp only [inner]
  conv_lhs => rw [sum4_swap]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [eps4_pair_swap ρ σ μ ν]

theorem lastDirectionWedge_lin_left (h : Fin 5) (X Y Z : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (α β : ℂ) :
    lastDirectionWedge h (fun μ ν a b => α * X μ ν a b + β * Y μ ν a b) Z =
      α * lastDirectionWedge h X Z + β * lastDirectionWedge h Y Z := by
  simp only [lastDirectionWedge, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem lastDirectionWedge_lin_right (h : Fin 5) (X Y Z : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (α β : ℂ) :
    lastDirectionWedge h Z (fun μ ν a b => α * X μ ν a b + β * Y μ ν a b) =
      α * lastDirectionWedge h Z X + β * lastDirectionWedge h Z Y := by
  rw [lastDirectionWedge_symm, lastDirectionWedge_lin_left, lastDirectionWedge_symm h X Z, lastDirectionWedge_symm h Y Z]

/-- **MacDowell–Mansouri with the form indices:** `(R − E/ℓ²) ∧ (R − E/ℓ²) = R∧R − (2/ℓ²)R∧E + (1/ℓ⁴)E∧E`. -/
theorem lastDirectionWedge_mm (h : Fin 5) (R E : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (ℓ : ℂ) :
    lastDirectionWedge h (fun μ ν a b => R μ ν a b - E μ ν a b / ℓ ^ 2)
        (fun μ ν a b => R μ ν a b - E μ ν a b / ℓ ^ 2) =
      lastDirectionWedge h R R - 2 / ℓ ^ 2 * lastDirectionWedge h R E + 1 / ℓ ^ 4 * lastDirectionWedge h E E := by
  have e : (fun μ ν a b => R μ ν a b - E μ ν a b / ℓ ^ 2) =
      (fun μ ν a b => 1 * R μ ν a b + (-(1 / ℓ ^ 2)) * E μ ν a b) := by
    funext μ ν a b
    ring
  rw [e, lastDirectionWedge_lin_left, lastDirectionWedge_lin_right, lastDirectionWedge_lin_right, lastDirectionWedge_symm h E R]
  ring

/-- **On the four directions that move the last-step direction, `ε_{habcd}` is `±ε_{abcd}`:** with the four directions numbered
in order (`Fin.succAbove h`), `ε_{h, a, b, c, d} = (−1)^h ε_{abcd}`. -/
theorem lc5_restrict : ∀ (h : Fin 5) (a b c d : Fin 4),
    lc5 h (h.succAbove a) (h.succAbove b) (h.succAbove c) (h.succAbove d) =
      (-1) ^ (h : ℕ) * WholePicture.eps4 a b c d := by
  decide +kernel

/-! ## The split is direct -/

theorem trace_fourZ : ∀ a b c d : Fin 5,
    (γZ a * γZ b * γZ c * γZ d).trace =
      4 * ((if a = b ∧ c = d then 1 else 0) - (if a = c ∧ b = d then 1 else 0) +
        (if a = d ∧ b = c then 1 else 0)) := by
  decide +kernel

/-- `tr(γ_aγ_bγ_cγ_d) = 4(δ_abδ_cd − δ_acδ_bd + δ_adδ_bc)`. -/
theorem trace_four (a b c d : Fin 5) :
    (γ a * γ b * γ c * γ d).trace =
      4 * ((if a = b ∧ c = d then 1 else 0) - (if a = c ∧ b = d then 1 else 0) +
        (if a = d ∧ b = c then 1 else 0)) := by
  have h := congrArg GaussianInt.toComplex (trace_fourZ a b c d)
  rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, γZ_map, γZ_map, γZ_map,
    γZ_map] at h
  rw [h, map_mul, show GaussianInt.toComplex 4 = 4 from map_ofNat _ 4]
  split_ifs <;> simp

/-- **The split is direct:** a combination of the six that is a combination of the four is zero, and so is the
combination of the four. -/
theorem split_direct (h : Fin 5) (X : Fin 5 → Fin 5 → ℂ) (y : Fin 5 → ℂ)
    (hXy : six (univ.erase h) X = four h (univ.erase h) y) :
    four h (univ.erase h) y = 0 ∧ six (univ.erase h) X = 0 := by
  have hy : ∀ d ∈ univ.erase h, y d = 0 := by
    intro d hd
    have hd' : d ≠ h := Finset.ne_of_mem_erase hd
    have t := congrArg (fun M => (M * (γ h * γ d)).trace) hXy
    simp only [six, four, Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul] at t
    have e6 : ∀ a ∈ univ.erase h, ∀ b ∈ univ.erase h, (γ a * γ b * (γ h * γ d)).trace = 0 := by
      intro a ha b hb
      have ha' : a ≠ h := Finset.ne_of_mem_erase ha
      have hb' : b ≠ h := Finset.ne_of_mem_erase hb
      rw [← Matrix.mul_assoc, trace_four]
      simp [ha', hb', Ne.symm hd']
    have e4 : ∀ c ∈ univ.erase h, (γ h * γ c * (γ h * γ d)).trace = if c = d then -4 else 0 := by
      intro c hc
      have hc' : c ≠ h := Finset.ne_of_mem_erase hc
      rw [← Matrix.mul_assoc, trace_four]
      by_cases hcd : c = d
      · subst hcd
        simp [Ne.symm hc']
      · simp [hcd, Ne.symm hc', Ne.symm hd']
    have hL : ∑ a ∈ univ.erase h, ∑ b ∈ univ.erase h, X a b * (γ a * γ b * (γ h * γ d)).trace = 0 :=
      Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by rw [e6 a ha b hb, mul_zero]
    have hR : ∑ c ∈ univ.erase h, y c * (γ h * γ c * (γ h * γ d)).trace = -4 * y d := by
      rw [Finset.sum_eq_single d]
      · rw [e4 d hd, if_pos rfl]
        ring
      · intro c hc hcd
        rw [e4 c hc, if_neg hcd, mul_zero]
      · intro hn
        exact absurd hd hn
    rw [hL, hR] at t
    simpa using t
  have h4 : four h (univ.erase h) y = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [hy d hd, zero_smul]
  exact ⟨h4, hXy.trans h4⟩

end Law

end Comparison.System
