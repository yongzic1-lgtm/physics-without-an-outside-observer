import Comparison.GroupsContinuumLaw.Spin5
import Comparison.Elements.Turns
import Comparison.Existence.Table

/-!
# P1's real six, and `U ↦ U ⊗ U` as a homomorphism `SU(4) → O(6)` (Prop. 17, part one)

P1's real six are the two-spinor states with the matrices `e₀ = J`, `e_{s+1} = i γ_s J`
(`Elements/SixDirections.lean`: `sixP1`); `U ⊗ U` acts on a two-spinor state of matrix `A` by
`A ↦ U A Uᵀ` (`Elements/TwoThings.lean`: `kron_mulVec_relOf`). With `⟨A, B⟩ = ¼ tr(A† B)`:

* `ip_six`: the six are orthonormal; `expand`: **every antisymmetric `X` is `Σ_a ⟨e_a, X⟩ e_a`**
  (checked on the six basic antisymmetric matrices over `ℤ[i]`);
* `pf_ιC`: `Pf(Σ z_a e_a) = Σ z_a²`; `pfb_conj`: the polarized Pfaffian is kept by `det U = 1`;
* `coord_real`: **for `U ∈ SU(4)` and a real point `t` of the six, the coordinates of `U ι(t) Uᵀ`
  are real**: `U ⊗ U` keeps P1's real six;
* `rot6Hom : SU(4) →* O(6)`, `ι6_rot6`: `U ι(t) Uᵀ = ι(R_U t)`; the length is the Pfaffian.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex Kronecker

noncomputable section

/-- P1's real six as a Euclidean space. -/
abbrev E6 := EuclideanSpace ℝ (Fin 6)

/-! ## The six over the Gaussian integers -/

/-- P1's real six over `ℤ[i]`. -/
def sixZ : Fin 6 → Matrix Four Four GaussianInt :=
  ![JZ, iZ • (γZ 0 * JZ), iZ • (γZ 1 * JZ), iZ • (γZ 2 * JZ), iZ • (γZ 3 * JZ), iZ • (γZ 4 * JZ)]

theorem map_smulZ (c : GaussianInt) (M : Matrix Four Four GaussianInt) :
    (c • M).map GaussianInt.toComplex = (GaussianInt.toComplex c) • M.map GaussianInt.toComplex := by
  ext i j
  simp

theorem toComplex_iZ : GaussianInt.toComplex iZ = I := by
  simp [iZ, GaussianInt.toComplex_def']

theorem sixZ_map (a : Fin 6) : (sixZ a).map GaussianInt.toComplex = sixP1 a := by
  fin_cases a <;>
    simp [sixZ, sixP1, map_smulZ, Matrix.map_mul, γZ_map, JZ_map, toComplex_iZ]

theorem map_conjTransposeZ (M : Matrix Four Four GaussianInt) :
    Mᴴ.map GaussianInt.toComplex = (M.map GaussianInt.toComplex)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, GaussianInt.toComplex_star]

theorem ip_sixZ : ∀ a b : Fin 6, ((sixZ a)ᴴ * sixZ b).trace = if a = b then 4 else 0 := by
  decide +kernel

/-- The six basic antisymmetric matrices. -/
def Bpq {R : Type*} [Ring R] (p q : Four) : Matrix Four Four R :=
  Matrix.single p q 1 - Matrix.single q p 1

theorem expand_sixZ : ∀ p q : Four,
    (4 : GaussianInt) • (Bpq p q : Matrix Four Four GaussianInt) =
      ∑ a, ((sixZ a)ᴴ * Bpq p q).trace • sixZ a := by
  decide +kernel

theorem Bpq_map (p q : Four) :
    (Bpq p q : Matrix Four Four GaussianInt).map GaussianInt.toComplex = Bpq p q := by
  ext i j
  simp only [Bpq, Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.single_apply,
    apply_ite GaussianInt.toComplex, map_one, map_zero]

theorem map_sum_smulZ (c : Fin 6 → GaussianInt) (M : Fin 6 → Matrix Four Four GaussianInt) :
    (∑ a, c a • M a).map GaussianInt.toComplex =
      ∑ a, GaussianInt.toComplex (c a) • (M a).map GaussianInt.toComplex := by
  ext i j
  simp [Matrix.sum_apply, map_sum]

/-! ## The Hermitian pairing and the expansion -/

/-- `⟨A, B⟩ = ¼ tr(A† B)`. -/
def ip (A B : Matrix Four Four ℂ) : ℂ := (1 / 4 : ℂ) * (Aᴴ * B).trace

theorem trace_map_toComplex (M : Matrix Four Four GaussianInt) :
    GaussianInt.toComplex M.trace = (M.map GaussianInt.toComplex).trace :=
  AddMonoidHom.map_trace GaussianInt.toComplex M

/-- **The six are orthonormal.** -/
theorem ip_six (a b : Fin 6) : ip (sixP1 a) (sixP1 b) = if a = b then 1 else 0 := by
  have h := congrArg GaussianInt.toComplex (ip_sixZ a b)
  rw [trace_map_toComplex, Matrix.map_mul, map_conjTransposeZ, sixZ_map, sixZ_map] at h
  rw [ip, h]
  split_ifs <;> norm_num [map_ofNat]

theorem expand_Bpq (p q : Four) :
    (Bpq p q : Matrix Four Four ℂ) = ∑ a, ip (sixP1 a) (Bpq p q) • sixP1 a := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (expand_sixZ p q)
  simp only [map_smulZ, map_sum_smulZ, Bpq_map, sixZ_map, trace_map_toComplex, Matrix.map_mul,
    map_conjTransposeZ] at h
  have h4 : GaussianInt.toComplex 4 = 4 := map_ofNat GaussianInt.toComplex 4
  rw [h4] at h
  calc (Bpq p q : Matrix Four Four ℂ) = (1 / 4 : ℂ) • ((4 : ℂ) • Bpq p q) := by
        rw [smul_smul]; norm_num
    _ = (1 / 4 : ℂ) • ∑ a, ((sixP1 a)ᴴ * Bpq p q).trace • sixP1 a := by rw [h]
    _ = ∑ a, ip (sixP1 a) (Bpq p q) • sixP1 a := by
        rw [Finset.smul_sum]
        simp only [smul_smul, ip]

/-- The pairing with a fixed matrix, as a linear map. -/
def ipL (A : Matrix Four Four ℂ) : Matrix Four Four ℂ →ₗ[ℂ] ℂ where
  toFun B := ip A B
  map_add' B C := by simp only [ip, Matrix.mul_add, Matrix.trace_add, mul_add]
  map_smul' c B := by
    simp only [ip, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem decomp (X : Matrix Four Four ℂ) (hX : Xᵀ = -X) :
    X = (1 / 2 : ℂ) • ∑ p, ∑ q, X p q • (Bpq p q : Matrix Four Four ℂ) := by
  have h1 : ∑ p, ∑ q, X p q • (Matrix.single p q (1 : ℂ)) = X := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have h2 : ∑ p, ∑ q, X p q • (Matrix.single q p (1 : ℂ)) = Xᵀ := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single Xᵀ]
    rw [Finset.sum_comm]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.transpose_apply]
  simp only [Bpq, smul_sub, Finset.sum_sub_distrib, h1, h2, hX, sub_neg_eq_add]
  rw [← two_smul ℂ X, smul_smul]
  norm_num

/-- **Every antisymmetric matrix is `Σ_a ⟨e_a, X⟩ e_a`.** -/
theorem expand (X : Matrix Four Four ℂ) (hX : Xᵀ = -X) :
    X = ∑ a, ip (sixP1 a) X • sixP1 a := by
  let Φ : Matrix Four Four ℂ →ₗ[ℂ] Matrix Four Four ℂ :=
    ∑ a, (ipL (sixP1 a)).smulRight (sixP1 a)
  have hΦ : ∀ Y, Φ Y = ∑ a, ip (sixP1 a) Y • sixP1 a := by
    intro Y
    change (∑ a, (ipL (sixP1 a)).smulRight (sixP1 a)) Y = _
    rw [LinearMap.sum_apply]
    rfl
  have hB : ∀ p q, Φ (Bpq p q) = Bpq p q := fun p q => by rw [hΦ]; exact (expand_Bpq p q).symm
  rw [← hΦ]
  conv_rhs => rw [decomp X hX]
  rw [map_smul, map_sum]
  simp only [map_sum, map_smul, hB]
  exact decomp X hX

/-! ## The real six -/

/-- The point of the six with complex coordinates `z`. -/
def ιC (z : Fin 6 → ℂ) : Matrix Four Four ℂ := ∑ a, z a • sixP1 a

/-- The point of the six with real coordinates `t`. -/
def ι6 (t : E6) : Matrix Four Four ℂ := ιC fun a => ((t a : ℝ) : ℂ)

theorem ιC_transpose (z : Fin 6 → ℂ) : (ιC z)ᵀ = -ιC z := by
  simp [ιC, Matrix.transpose_sum, Matrix.transpose_smul, sixP1_transpose, Finset.sum_neg_distrib]

theorem ip_ιC_right (A : Matrix Four Four ℂ) (z : Fin 6 → ℂ) :
    ip A (ιC z) = ∑ b, z b * ip A (sixP1 b) := by
  rw [ip, ιC, Matrix.mul_sum, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, ip, smul_eq_mul]
  ring

theorem ip_ιC (a : Fin 6) (z : Fin 6 → ℂ) : ip (sixP1 a) (ιC z) = z a := by
  rw [ip_ιC_right]
  simp [ip_six]

theorem ιC_injective : Function.Injective ιC := by
  intro y z h
  funext a
  rw [← ip_ιC a y, h, ip_ιC]

theorem ιC_add (y z : Fin 6 → ℂ) : ιC (y + z) = ιC y + ιC z := by
  simp [ιC, add_smul, Finset.sum_add_distrib]

theorem sixP1_eq_ιC (a : Fin 6) : sixP1 a = ιC (Pi.single a 1) := by
  simp [ιC, Pi.single_apply]

theorem expand_ιC (X : Matrix Four Four ℂ) (hX : Xᵀ = -X) :
    X = ιC fun a => ip (sixP1 a) X := expand X hX

/-- **`Pf(Σ z_a e_a) = Σ z_a²`.** -/
theorem pf_ιC (z : Fin 6 → ℂ) : pf (ιC z) = ∑ a, z a ^ 2 := by
  have h := pf_P1_six (z 0) (fun s => z s.succ)
  beta_reduce at h
  rw [pf_J, div_one] at h
  have e : ιC z = z 0 • J + ∑ s : Fin 5, z s.succ • (I • (γ s * J)) := by
    rw [ιC, Fin.sum_univ_succ, sixP1_zero]
    simp only [sixP1_succ]
  rw [e, h]
  exact (Fin.sum_univ_succ (fun a => z a ^ 2)).symm

/-- The polarized Pfaffian. -/
def pfb (A B : Matrix Four Four ℂ) : ℂ := pf (A + B) - pf A - pf B

theorem pfb_conj (U A B : Matrix Four Four ℂ) (hA : Aᵀ = -A) (hB : Bᵀ = -B) :
    pfb (U * A * Uᵀ) (U * B * Uᵀ) = U.det * pfb A B := by
  have hAB : (A + B)ᵀ = -(A + B) := by rw [Matrix.transpose_add, hA, hB, neg_add]
  have e : U * A * Uᵀ + U * B * Uᵀ = U * (A + B) * Uᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [pfb, pfb, e, pf_conj U _ hAB, pf_conj U _ hA, pf_conj U _ hB]
  ring

theorem pfb_ιC (y z : Fin 6 → ℂ) : pfb (ιC y) (ιC z) = 2 * ∑ a, y a * z a := by
  rw [pfb, ← ιC_add, pf_ιC, pf_ιC, pf_ιC, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]
  ring

theorem ip_conj (A B : Matrix Four Four ℂ) : star (ip A B) = ip B A := by
  rw [ip, ip, star_mul', ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp

theorem ip_adjoint (M A B : Matrix Four Four ℂ) :
    ip (M * A * Mᵀ) B = ip A (Mᴴ * B * (Mᴴ)ᵀ) := by
  have hT : (Mᵀ)ᴴ = (Mᴴ)ᵀ := by ext i j; simp
  rw [ip, ip, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT]
  congr 1
  rw [show (Mᴴ)ᵀ * (Aᴴ * Mᴴ) * B = (Mᴴ)ᵀ * (Aᴴ * Mᴴ * B) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem ip_ιC_left (z : Fin 6 → ℂ) (Y : Matrix Four Four ℂ) :
    ip (ιC z) Y = ∑ b, star (z b) * ip (sixP1 b) Y := by
  rw [ip, ιC, Matrix.conjTranspose_sum, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, ip, smul_eq_mul]
  ring

/-- The `SU(4)` rotations. -/
abbrev SU4 := Matrix.specialUnitaryGroup Four ℂ

theorem su4_unitary (U : SU4) : (U : Matrix Four Four ℂ) * star (U : Matrix Four Four ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp U.2.1

theorem su4_unitary_left (U : SU4) :
    star (U : Matrix Four Four ℂ) * (U : Matrix Four Four ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp U.2.1

theorem su4_det (U : SU4) : (U : Matrix Four Four ℂ).det = 1 := U.2.2

theorem conjT_mul_transpose (M : Matrix Four Four ℂ) (h : M * star M = 1) :
    (star M)ᵀ * Mᵀ = 1 := by
  rw [← Matrix.transpose_mul, h, Matrix.transpose_one]

/-- **The coordinates of `U ι(t) Uᵀ` are real**: `U ⊗ U` keeps P1's real six. -/
theorem coord_real (U : SU4) (t : E6) (a : Fin 6) :
    star (ip (sixP1 a) ((U : Matrix Four Four ℂ) * ι6 t * (U : Matrix Four Four ℂ)ᵀ)) =
      ip (sixP1 a) ((U : Matrix Four Four ℂ) * ι6 t * (U : Matrix Four Four ℂ)ᵀ) := by
  set M : Matrix Four Four ℂ := (U : Matrix Four Four ℂ) with hM
  set X := M * ι6 t * Mᵀ with hX
  have hXa : Xᵀ = -X := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ι6,
      ιC_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  set Y := Mᴴ * sixP1 a * (Mᴴ)ᵀ with hY
  have hYa : Yᵀ = -Y := by
    rw [hY, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      sixP1_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hMY : M * Y * Mᵀ = sixP1 a := by
    have h1 := su4_unitary U
    have h2 := conjT_mul_transpose M h1
    rw [hY, ← Matrix.star_eq_conjTranspose]
    calc M * (star M * sixP1 a * (star M)ᵀ) * Mᵀ
        = (M * star M) * sixP1 a * ((star M)ᵀ * Mᵀ) := by simp only [Matrix.mul_assoc]
      _ = sixP1 a := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  set y : Fin 6 → ℂ := fun b => ip (sixP1 b) Y with hy
  have hYι : Y = ιC y := expand_ιC Y hYa
  have h1 : 2 * ip (sixP1 a) X = 2 * ∑ b, y b * ((t b : ℝ) : ℂ) := by
    have hXι : X = ιC fun b => ip (sixP1 b) X := expand_ιC X hXa
    have e1 : pfb (sixP1 a) X = 2 * ip (sixP1 a) X := by
      have := pfb_ιC (Pi.single a 1) (fun b => ip (sixP1 b) X)
      rw [← sixP1_eq_ιC a, ← hXι] at this
      rw [this]
      simp [Pi.single_apply]
    have e2 : pfb (sixP1 a) X = pfb Y (ι6 t) := by
      rw [← hMY, hX, pfb_conj M Y (ι6 t) hYa (by rw [ι6]; exact ιC_transpose _), su4_det U,
        one_mul]
    rw [← e1, e2, hYι, ι6, pfb_ιC]
  have h2 : star (ip (sixP1 a) X) = ∑ b, y b * ((t b : ℝ) : ℂ) := by
    rw [ip_conj, hX, ip_adjoint, ← hY, ι6, ip_ιC_left]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.conj_ofReal, mul_comm]
  have h1' : ip (sixP1 a) X = ∑ b, y b * ((t b : ℝ) : ℂ) := by
    have := congrArg (fun z : ℂ => z / 2) h1
    simpa using this
  rw [h2, h1']

/-! ## The rotation of a rotation on the six -/

/-- `R_U t`: the coordinates of `U ι(t) Uᵀ`. -/
def rot6V (U : SU4) (t : E6) : E6 :=
  WithLp.toLp 2 fun a => (ip (sixP1 a) ((U : Matrix Four Four ℂ) * ι6 t *
    (U : Matrix Four Four ℂ)ᵀ)).re

theorem ofReal_re_of_star (z : ℂ) (h : star z = z) : ((z.re : ℝ) : ℂ) = z := by
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

/-- **`U ι(t) Uᵀ = ι(R_U t)`.** -/
theorem ι6_rot6 (U : SU4) (t : E6) :
    ι6 (rot6V U t) = (U : Matrix Four Four ℂ) * ι6 t * (U : Matrix Four Four ℂ)ᵀ := by
  have hXa : ((U : Matrix Four Four ℂ) * ι6 t * (U : Matrix Four Four ℂ)ᵀ)ᵀ =
      -((U : Matrix Four Four ℂ) * ι6 t * (U : Matrix Four Four ℂ)ᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ι6,
      ιC_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  conv_rhs => rw [expand_ιC _ hXa]
  rw [ι6, rot6V]
  congr 1
  funext a
  simp only [PiLp.toLp_apply]
  exact ofReal_re_of_star _ (coord_real U t a)

theorem ι6_injective : Function.Injective ι6 := by
  intro s t h
  have h' := ιC_injective h
  apply WithLp.ofLp_injective 2
  funext a
  have := congrFun h' a
  exact_mod_cast this

theorem ι6_add (s t : E6) : ι6 (s + t) = ι6 s + ι6 t := by
  rw [ι6, ι6, ι6, ← ιC_add]
  congr 1
  funext a
  simp

theorem ι6_smul (c : ℝ) (t : E6) : ι6 (c • t) = (c : ℂ) • ι6 t := by
  simp only [ι6, ιC, Finset.smul_sum, smul_smul, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]

theorem pf_ι6 (t : E6) : pf (ι6 t) = ((∑ a, t a ^ 2 : ℝ) : ℂ) := by
  rw [ι6, pf_ιC]
  push_cast
  try rfl

theorem rot6V_add (U : SU4) (s t : E6) : rot6V U (s + t) = rot6V U s + rot6V U t := by
  apply ι6_injective
  rw [ι6_add, ι6_rot6, ι6_rot6, ι6_rot6, ι6_add, Matrix.mul_add, Matrix.add_mul]

theorem rot6V_smul (U : SU4) (c : ℝ) (t : E6) : rot6V U (c • t) = c • rot6V U t := by
  apply ι6_injective
  rw [ι6_smul, ι6_rot6, ι6_rot6, ι6_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem rot6V_sumsq (U : SU4) (t : E6) : ∑ a, rot6V U t a ^ 2 = ∑ a, t a ^ 2 := by
  have h := pf_ι6 (rot6V U t)
  rw [ι6_rot6, pf_conj _ _ (by rw [ι6]; exact ιC_transpose _), su4_det, one_mul, pf_ι6] at h
  exact_mod_cast h.symm

theorem rot6V_norm (U : SU4) (t : E6) : ‖rot6V U t‖ = ‖t‖ := by
  have h : ‖rot6V U t‖ ^ 2 = ‖t‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, rot6V_sumsq]
  rw [← Real.sqrt_sq (norm_nonneg (rot6V U t)), ← Real.sqrt_sq (norm_nonneg t), h]

/-- `R_U` as a linear isometry of the six. -/
def rot6LI (U : SU4) : E6 →ₗᵢ[ℝ] E6 where
  toFun := rot6V U
  map_add' := rot6V_add U
  map_smul' := fun c x => by rw [RingHom.id_apply]; exact rot6V_smul U c x
  norm_map' := rot6V_norm U

/-- `R_U ∈ O(6)`. -/
def rot6E (U : SU4) : E6 ≃ₗᵢ[ℝ] E6 := (rot6LI U).toLinearIsometryEquiv rfl

theorem rot6E_apply (U : SU4) (t : E6) : rot6E U t = rot6V U t := rfl

theorem rot6V_one (t : E6) : rot6V 1 t = t := by
  apply ι6_injective
  rw [ι6_rot6]
  simp

theorem rot6V_mul (U V : SU4) (t : E6) : rot6V (U * V) t = rot6V U (rot6V V t) := by
  apply ι6_injective
  rw [ι6_rot6, ι6_rot6, ι6_rot6]
  change (U : Matrix Four Four ℂ) * (V : Matrix Four Four ℂ) * ι6 t *
    ((U : Matrix Four Four ℂ) * (V : Matrix Four Four ℂ))ᵀ = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **`U ↦ U ⊗ U` on P1's real six is a homomorphism `SU(4) → O(6)`.** -/
def rot6Hom : SU4 →* (E6 ≃ₗᵢ[ℝ] E6) where
  toFun := rot6E
  map_one' := LinearIsometryEquiv.ext fun x => by rw [rot6E_apply, rot6V_one]; rfl
  map_mul' := fun U V => LinearIsometryEquiv.ext fun x => by
    rw [rot6E_apply, rot6V_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, rot6E_apply,
      rot6E_apply]

theorem rot6Hom_apply (U : SU4) (t : E6) : rot6Hom U t = rot6V U t := rfl

/-- In the two-system language: `U ⊗ U` carries the two-spinor state of `ι(t)` to that of `ι(R_U t)`. -/
theorem kron_six (U : SU4) (t : E6) :
    ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) *ᵥ relOf (ι6 t) =
      relOf (ι6 (rot6Hom U t)) := by
  rw [kron_mulVec_relOf, rot6Hom_apply, ι6_rot6]

end

end Comparison.GroupsContinuumLaw
