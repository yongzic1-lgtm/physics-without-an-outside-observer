import Comparison.System.Geometry.Definitions
import Comparison.Article.DimQ
import Comparison.GroupsContinuumLaw.Twistor
import Comparison.GroupsContinuumLaw.Spin6

/-!
# The geometry of comparison, Book I: one system (Propositions 1 to 8)

* `prop_1`: for **every** system `(H, Θ)`: `⟨v, Θv⟩ = 0`, `‖Θv‖ = ‖v‖`; in every orthonormal basis
  `Θv = J v̄` with `J` unitary and `Jᵀ = −J`; a normal basis `u₁, −Θu₁, …` with the matrix `J_n`,
  `dim H = 2n`; `i`, `Θ`, `iΘ` act as the quaternion units and `H = ℍⁿ`.
* `prop_2`: for every `(H, Θ)` with `dim H = 2n`: `dim Q = 2n² − n − 1` and `Q ≅ Herm₀(ℍⁿ)`.
* `prop_3`: `Q ≠ 0` and `a² = τ(a²)·1` for every `a ∈ Q` exactly when `dim H = 4`; then `dim Q = 5`.
* `prop_4` to `prop_8`: perpendicular lines anticommute and five orthonormal lines multiply to
  `det = ±1`; the two sides; the ten rotations; the overlap; the sphere of lines.
-/

open scoped InnerProductSpace Quaternion Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

section OneThing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Proposition 1: the quaternionic structure in every basis -/

/-- **`Θ v = J_b v̄` in every orthonormal basis.** -/
theorem partnerMatrix_coord (T : Partner H) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (v : H) (i : ι) :
    ⟪b i, T.Θ v⟫_ℂ = (partnerMatrix T b *ᵥ star (fun j => ⟪b j, v⟫_ℂ)) i := by
  conv_lhs => rw [← b.sum_repr' v]
  rw [partner_sum, inner_sum]
  simp only [T.map_smul, inner_smul_right, Matrix.mulVec, dotProduct, partnerMatrix, Matrix.of_apply,
    Pi.star_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **The matrix of the quaternionic structure is antisymmetric in every orthonormal basis:** `J_bᵀ = −J_b`. -/
theorem partnerMatrix_transpose (T : Partner H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) : (partnerMatrix T b)ᵀ = -partnerMatrix T b := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, partnerMatrix, Matrix.of_apply]
  have h := T.inner_Θ (b j) (T.Θ (b i))
  rw [T.Θ_Θ, inner_neg_right] at h
  have h' := congrArg (starRingEnd ℂ) h
  rw [map_neg, inner_conj_symm, inner_conj_symm] at h'
  rw [← h']

/-- **The matrix of the quaternionic structure is unitary in every orthonormal basis.** -/
theorem partnerMatrix_unitary (T : Partner H) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H) : (partnerMatrix T b)ᴴ * partnerMatrix T b = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partnerMatrix, Matrix.of_apply,
    Matrix.one_apply]
  have hP := b.sum_inner_mul_inner (T.Θ (b j)) (T.Θ (b l))
  have e : ∀ i, star ⟪b i, T.Θ (b j)⟫_ℂ = ⟪T.Θ (b j), b i⟫_ℂ := fun i => inner_conj_symm _ _
  simp only [e]
  rw [hP, T.inner_Θ]
  rw [orthonormal_iff_ite.mp b.orthonormal l j]
  by_cases h : j = l
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **In a normal basis the matrix of the quaternionic structure is `J_n = diag(ε, …, ε)`.** -/
theorem partnerMatrix_normal (T : Partner H) {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) : partnerMatrix T b = Jn n := by
  ext p q
  have h1 := partnerMatrix_coord T b (b q) p
  have h2 := T.coord_Θ b hb (b q) p
  have hc : (fun j => star ⟪b j, b q⟫_ℂ) = (Pi.single q 1 : Fin n × Fin 2 → ℂ) := by
    funext j
    rw [orthonormal_iff_ite.mp b.orthonormal j q]
    by_cases h : j = q
    · subst h; simp
    · simp [h]
  have h1' : ⟪b p, T.Θ (b q)⟫_ℂ = (partnerMatrix T b *ᵥ Pi.single q 1) p := by
    rw [h1, ← hc]; rfl
  rw [hc] at h2
  rw [Matrix.mulVec_single_one] at h1' h2
  rw [h1'] at h2
  simpa [Matrix.col_apply] using h2

/-! ## Proposition 1: the quaternionic structure -/

/-- Multiplication by `i`, a real-linear map of `H`. -/
noncomputable def imulR : Module.End ℝ H where
  toFun v := Complex.I • v
  map_add' v w := smul_add _ v w
  map_smul' r v := smul_comm Complex.I r v

/-- The quaternionic structure, a real-linear map of `H`. -/
noncomputable def partnerR (T : Partner H) : Module.End ℝ H where
  toFun := T.Θ
  map_add' := T.map_add
  map_smul' r v := partner_real_smul T r v

theorem imulR_apply (v : H) : (imulR : Module.End ℝ H) v = Complex.I • v := rfl

theorem partnerR_apply (T : Partner H) (v : H) : partnerR T v = T.Θ v := rfl

/-- **`i`, `Θ` and `iΘ` multiply as the quaternion units:** `i² = Θ² = −1`, `Θ i = −i Θ`. -/
noncomputable def quatBasis (T : Partner H) :
    QuaternionAlgebra.Basis (Module.End ℝ H) (-1 : ℝ) 0 (-1) where
  i := imulR
  j := partnerR T
  k := imulR * partnerR T
  i_mul_i := by
    ext v
    simp [imulR_apply, smul_smul]
  j_mul_j := by
    ext v
    simp [partnerR_apply, T.Θ_Θ]
  i_mul_j := rfl
  j_mul_i := by
    ext v
    simp only [Module.End.mul_apply, imulR_apply, partnerR_apply, T.map_smul, Complex.star_def,
      Complex.conj_I, zero_smul, zero_sub, LinearMap.neg_apply, neg_smul]

/-- **The quaternions act on every system with a quaternionic structure:** `i ↦ (i·)`, `j ↦ Θ`, `k ↦ iΘ`. -/
noncomputable def quatAction (T : Partner H) : ℍ[ℝ] →ₐ[ℝ] Module.End ℝ H := (quatBasis T).liftHom

theorem quatAction_apply (T : Partner H) (q : ℍ[ℝ]) (v : H) :
    quatAction T q v = q.re • v + q.imI • (Complex.I • v) + q.imJ • T.Θ v +
      q.imK • (Complex.I • T.Θ v) := by
  simp [quatAction, QuaternionAlgebra.Basis.lift, quatBasis, imulR_apply, partnerR_apply,
    Algebra.algebraMap_eq_smul_one]

theorem smul_eq_complex (r : ℝ) (v : H) : r • v = (r : ℂ) • v := rfl

/-- The quaternion `q` acts as `α v + β Θv`, `α = re + imI i`, `β = imJ + imK i`. -/
theorem quatAction_eq (T : Partner H) (q : ℍ[ℝ]) (v : H) :
    quatAction T q v = (⟨q.re, q.imI⟩ : ℂ) • v + (⟨q.imJ, q.imK⟩ : ℂ) • T.Θ v := by
  rw [quatAction_apply]
  have e1 : (⟨q.re, q.imI⟩ : ℂ) = (q.re : ℂ) + (q.imI : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have e2 : (⟨q.imJ, q.imK⟩ : ℂ) = (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [e1, e2, add_smul, add_smul, mul_smul, mul_smul, smul_eq_complex, smul_eq_complex q.imI,
    smul_eq_complex q.imJ, smul_eq_complex q.imK]
  abel

/-- The quaternion with complex parts `α = re + imI·i` and `β = imJ + imK·i`. -/
def quatOf (α β : ℂ) : ℍ[ℝ] := ⟨α.re, α.im, β.re, β.im⟩

/-- **The quaternionic coordinates** `(q₁, …, q_n) ↦ Σ_k q_k · u_k`. -/
noncomputable def quatCoords (T : Partner H) {n : ℕ} (u : Fin n → H) : (Fin n → ℍ[ℝ]) → H :=
  fun q => ∑ k, quatAction T (q k) (u k)

/-- The quaternionic coordinates in a normal basis, as a map back from `H`. -/
noncomputable def quatCoordsInv {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H) (v : H) :
    Fin n → ℍ[ℝ] :=
  fun k => quatOf ⟪b (k, 0), v⟫_ℂ (-⟪b (k, 1), v⟫_ℂ)

theorem quatCoords_normal (T : Partner H) {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) (q : Fin n → ℍ[ℝ]) :
    quatCoords T (fun k => b (k, 0)) q =
      ∑ k, ((⟨(q k).re, (q k).imI⟩ : ℂ) • b (k, 0) - (⟨(q k).imJ, (q k).imK⟩ : ℂ) • b (k, 1)) := by
  unfold quatCoords
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [quatAction_eq, hb k, smul_neg, sub_neg_eq_add]

/-- **`H = ℍⁿ`:** in a normal basis the quaternionic coordinates are a bijection `ℍⁿ → H`. -/
theorem quatCoords_bijective (T : Partner H) {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) :
    Function.Bijective (quatCoords T (fun k => b (k, 0))) := by
  have hcoord : ∀ (q : Fin n → ℍ[ℝ]) (k : Fin n),
      ⟪b (k, 0), quatCoords T (fun k => b (k, 0)) q⟫_ℂ = (⟨(q k).re, (q k).imI⟩ : ℂ) ∧
      ⟪b (k, 1), quatCoords T (fun k => b (k, 0)) q⟫_ℂ = -(⟨(q k).imJ, (q k).imK⟩ : ℂ) := by
    intro q k
    rw [quatCoords_normal T b hb]
    simp only [inner_sum, inner_sub_right, inner_smul_right]
    simp only [orthonormal_iff_ite.mp b.orthonormal, Prod.mk.injEq]
    constructor
    · simp
    · simp
  constructor
  · intro q q' h
    funext k
    obtain ⟨h1, h2⟩ := hcoord q k
    obtain ⟨h1', h2'⟩ := hcoord q' k
    rw [h] at h1 h2
    rw [h1] at h1'
    rw [h2, neg_inj] at h2'
    have e1 := congrArg Complex.re h1'
    have e2 := congrArg Complex.im h1'
    have e3 := congrArg Complex.re h2'
    have e4 := congrArg Complex.im h2'
    simp only at e1 e2 e3 e4
    ext <;> simp [e1, e2, e3, e4]
  · intro v
    refine ⟨quatCoordsInv b v, ?_⟩
    rw [quatCoords_normal T b hb]
    conv_rhs => rw [← b.sum_repr' v]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two]
    simp only [quatCoordsInv, quatOf]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    all_goals (apply Complex.ext <;> simp)

/-- **`H` is a left `ℍ`-module through the coordinates.** -/
theorem quatCoords_mul (T : Partner H) {n : ℕ} (u : Fin n → H) (p : ℍ[ℝ]) (q : Fin n → ℍ[ℝ]) :
    quatCoords T u (fun k => p * q k) = quatAction T p (quatCoords T u q) := by
  unfold quatCoords
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Module.End.mul_apply]

/-! ## Proposition 2: the distinctions of every system -/

variable [FiniteDimensional ℂ H]

/-- The matrix of an operator in an orthonormal basis, as a real-linear equivalence. -/
noncomputable def matR {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H) :
    (H →ₗ[ℂ] H) ≃ₗ[ℝ] Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  ((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearEquiv).restrictScalars ℝ

theorem matR_apply {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H) (a : H →ₗ[ℂ] H) :
    matR b a = LinearMap.toMatrixOrthonormal b a := rfl

/-- In a normal basis the distinctions of `(H, Θ)` are carried onto the model's. -/
theorem map_distinctionsH (T : Partner H) {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) :
    (distinctionsH T).map (matR b).toLinearMap = Comparison.Article.distinctions n := by
  ext M
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Comparison.Article.mem_distinctions _).mpr ((T.isDistinctionH_iff b hb a).mp ha)
  · intro hM
    obtain ⟨a, rfl⟩ := (matR b).surjective M
    exact ⟨a, (T.isDistinctionH_iff b hb a).mpr ((Comparison.Article.mem_distinctions _).mp hM),
      rfl⟩

/-- **`dim Q = 2n² − n − 1`** for every system with `dim H = 2n`, `n ≥ 1`. -/
theorem finrank_distinctionsH (T : Partner H) {n : ℕ} (hn : 0 < n)
    (hdim : finrank ℂ H = 2 * n) : finrank ℝ (distinctionsH T) = 2 * n ^ 2 - n - 1 := by
  obtain ⟨m, b, hb⟩ := T.exists_normal_basis
  have hm : m = n := by have := Partner.finrank_eq b; omega
  subst hm
  rw [← Comparison.Article.finrank_distinctions m hn, ← map_distinctionsH T b hb]
  exact (Submodule.equivMapOfInjective _ (matR b).injective _).finrank_eq

end OneThing

/-! ## Proposition 2: `Q = Herm₀(ℍⁿ)` -/

/-- The quaternion `q` as the complex block `[[α, β], [−β̄, ᾱ]]`, `α = re + imI·i`, `β = imJ + imK·i`. -/
def qmat (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  Comparison.Article.qblock ⟨q.re, q.imI⟩ ⟨q.imJ, q.imK⟩

/-- A quaternionic `n × n` matrix as a complex `2n × 2n` matrix, block by block. -/
def qblockMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  Matrix.of fun p q => qmat (M p.1 q.1) p.2 q.2

theorem qstar_smul (r : ℝ) (q : ℍ[ℝ]) : star (r • q) = r • star q := by
  ext <;> simp

/-- **`Herm₀(ℍⁿ)`:** the Hermitian quaternionic `n × n` matrices of trace zero. -/
def hermZeroQ (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℍ[ℝ]) where
  carrier := {M | Mᴴ = M ∧ (M.trace).re = 0}
  add_mem' {M N} hM hN := by
    refine ⟨by rw [Matrix.conjTranspose_add, hM.1, hN.1], ?_⟩
    rw [Matrix.trace_add, QuaternionAlgebra.re_add, hM.2, hN.2, add_zero]
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' r M hM := by
    refine ⟨?_, ?_⟩
    · refine Matrix.ext fun i j => ?_
      have h := congrFun (congrFun hM.1 i) j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply] at h ⊢
      rw [qstar_smul, h]
    · rw [Matrix.trace_smul, QuaternionAlgebra.re_smul, hM.2, smul_zero]

theorem qblockMat_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    qblockMat (M + N) = qblockMat M + qblockMat N := by
  ext ⟨i, s⟩ ⟨j, t⟩
  fin_cases s <;> fin_cases t <;>
    simp [qblockMat, qmat, Comparison.Article.qblock, Complex.ext_iff] <;> ring_nf

theorem qblockMat_smul {n : ℕ} (r : ℝ) (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    qblockMat (r • M) = r • qblockMat M := by
  ext ⟨i, s⟩ ⟨j, t⟩
  fin_cases s <;> fin_cases t <;>
    simp [qblockMat, qmat, Comparison.Article.qblock, Complex.ext_iff]

/-- The block map as a real-linear map. -/
def qblockL (n : ℕ) :
    Matrix (Fin n) (Fin n) ℍ[ℝ] →ₗ[ℝ] Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ where
  toFun := qblockMat
  map_add' := qblockMat_add
  map_smul' := qblockMat_smul

theorem qblockMat_injective {n : ℕ} : Function.Injective (qblockMat (n := n)) := by
  intro M N h
  ext i j
  · have h0 := congrFun (congrFun h (i, 0)) (j, 0)
    simp only [qblockMat, qmat, Comparison.Article.qblock, Matrix.of_apply] at h0
    simpa using (Complex.ext_iff.mp h0).1
  · have h0 := congrFun (congrFun h (i, 0)) (j, 0)
    simp only [qblockMat, qmat, Comparison.Article.qblock, Matrix.of_apply] at h0
    simpa using (Complex.ext_iff.mp h0).2
  · have h0 := congrFun (congrFun h (i, 0)) (j, 1)
    simp only [qblockMat, qmat, Comparison.Article.qblock, Matrix.of_apply] at h0
    simpa using (Complex.ext_iff.mp h0).1
  · have h0 := congrFun (congrFun h (i, 0)) (j, 1)
    simp only [qblockMat, qmat, Comparison.Article.qblock, Matrix.of_apply] at h0
    simpa using (Complex.ext_iff.mp h0).2

theorem trace_qblockMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    (qblockMat M).trace = ((2 * (M.trace).re : ℝ) : ℂ) := by
  have hre : (M.trace).re = ∑ i, (M i i).re := by
    rw [Matrix.trace]
    exact map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ _
  rw [hre, Finset.mul_sum]
  simp only [Matrix.trace, Matrix.diag, qblockMat, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, qmat, Comparison.Article.qblock]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem qblockMat_conjTranspose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    (qblockMat M)ᴴ = qblockMat Mᴴ := by
  ext ⟨i, s⟩ ⟨j, t⟩
  fin_cases s <;> fin_cases t <;>
    simp [qblockMat, qmat, Comparison.Article.qblock, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem qblockMat_commutes {n : ℕ} (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    qblockMat M * Jn n = Jn n * (qblockMat M).map star := by
  ext ⟨i, s⟩ ⟨j, t⟩
  rw [Comparison.Article.mul_Jn_apply, Comparison.Article.Jn_mul_apply]
  fin_cases s <;> fin_cases t <;>
    simp [qblockMat, qmat, Comparison.Article.qblock, ε, Complex.ext_iff]

/-- **The distinctions of the model `ℂ^{2n}` are the blocks of `Herm₀(ℍⁿ)`.** -/
theorem qblockMat_mem_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    IsDistinctionN n (qblockMat M) ↔ M ∈ hermZeroQ n := by
  constructor
  · rintro ⟨h1, h2, -⟩
    refine ⟨qblockMat_injective (by rw [← qblockMat_conjTranspose, h1]), ?_⟩
    rw [trace_qblockMat] at h2
    have := congrArg Complex.re h2
    simp at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [qblockMat_conjTranspose, h1], by rw [trace_qblockMat, h2]; simp,
      qblockMat_commutes M⟩

/-- Every distinction of the model `ℂ^{2n}` is a quaternionic block matrix. -/
theorem exists_qblockMat {n : ℕ} (a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (ha : IsDistinctionN n a) : ∃ M, qblockMat M = a := by
  obtain ⟨h1, -, h3⟩ := ha
  refine ⟨Matrix.of fun i j => ⟨(a (i, 0) (j, 0)).re, (a (i, 0) (j, 0)).im,
    (a (i, 0) (j, 1)).re, (a (i, 0) (j, 1)).im⟩, ?_⟩
  ext ⟨i, s⟩ ⟨j, t⟩
  have hr := Comparison.Article.W_rel h3 i j
  fin_cases s <;> fin_cases t <;>
    simp [qblockMat, qmat, Comparison.Article.qblock, hr.1, hr.2, Complex.ext_iff]

/-- The block map on `Herm₀(ℍⁿ)`, into the distinctions of `ℂ^{2n}`. -/
noncomputable def toDistinctions (n : ℕ) : hermZeroQ n →ₗ[ℝ] Comparison.Article.distinctions n :=
  ((qblockL n).domRestrict (hermZeroQ n)).codRestrict (Comparison.Article.distinctions n)
    (fun M => (Comparison.Article.mem_distinctions _).mpr ((qblockMat_mem_iff M.1).mpr M.2))

theorem toDistinctions_apply (n : ℕ) (M : hermZeroQ n) :
    (toDistinctions n M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) = qblockMat M.1 := rfl

/-- **`Q ≅ Herm₀(ℍⁿ)`** on the model `ℂ^{2n}`. -/
noncomputable def distinctionsEquivHermZeroQ (n : ℕ) :
    hermZeroQ n ≃ₗ[ℝ] Comparison.Article.distinctions n :=
  LinearEquiv.ofBijective (toDistinctions n)
    ⟨fun M N h => Subtype.ext (qblockMat_injective (by
        have := congrArg Subtype.val h
        rwa [toDistinctions_apply, toDistinctions_apply] at this)), fun a => by
      have ha := (Comparison.Article.mem_distinctions _).mp a.2
      obtain ⟨M, hM⟩ := exists_qblockMat a.1 ha
      have hmem : M ∈ hermZeroQ n := (qblockMat_mem_iff M).mp (by rw [hM]; exact ha)
      exact ⟨⟨M, hmem⟩, Subtype.ext (by rw [toDistinctions_apply]; exact hM)⟩⟩

section OneThing2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **`Q(H) ≅ Herm₀(ℍⁿ)`** for every system, through a normal basis. -/
noncomputable def distinctionsH_equiv (T : Partner H) {n : ℕ}
    (b : OrthonormalBasis (Fin n × Fin 2) ℂ H) (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) :
    distinctionsH T ≃ₗ[ℝ] hermZeroQ n :=
  ((Submodule.equivMapOfInjective _ (matR b).injective _).trans
    (LinearEquiv.ofEq _ _ (map_distinctionsH T b hb))).trans (distinctionsEquivHermZeroQ n).symm

/-! ## Proposition 3 -/

theorem τH_smul_one (c : ℂ) (h : finrank ℂ H ≠ 0) : τH (c • (1 : H →ₗ[ℂ] H)) = c := by
  rw [τH, map_smul, LinearMap.trace_one, smul_eq_mul]
  have : (finrank ℂ H : ℂ) ≠ 0 := by exact_mod_cast h
  field_simp

theorem finrank_ne_zero_of_exists (T : Partner H) (h : ∃ a, T.IsDistinctionH a ∧ a ≠ 0) :
    finrank ℂ H ≠ 0 := by
  intro h0
  obtain ⟨a, -, ha⟩ := h
  apply ha
  have : Subsingleton H := Module.finrank_zero_iff.mp h0
  ext v
  simp [Subsingleton.elim v 0]

/-- P3 (b) with `a² = c·1`, `c` real, is P3 (b) with `a² = τ(a²)·1`. -/
theorem P3H_iff_tau (T : Partner H) :
    T.P3H ↔ ((∃ a, T.IsDistinctionH a ∧ a ≠ 0) ∧
      ∀ a, T.IsDistinctionH a → a * a = τH (a * a) • (1 : H →ₗ[ℂ] H)) := by
  constructor
  · rintro ⟨hne, hsq⟩
    refine ⟨hne, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := hsq a ha
    rw [hc, τH_smul_one _ (finrank_ne_zero_of_exists T hne)]
  · rintro ⟨hne, hsq⟩
    refine ⟨hne, fun a ha => ?_⟩
    have hd := finrank_ne_zero_of_exists T hne
    have e := hsq a ha
    set z := τH (a * a) with hz
    have hnt : Nontrivial H := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hd)
    have hstar : star (a * a) = a * a := by rw [star_mul, ha.1.star_eq]
    have h1 : star z • (1 : H →ₗ[ℂ] H) = z • (1 : H →ₗ[ℂ] H) := by
      have h2 := congrArg star e
      rw [hstar, star_smul, star_one] at h2
      rw [← h2, ← e]
    have h3 : (star z - z) • (1 : H →ₗ[ℂ] H) = 0 := by rw [sub_smul, h1, sub_self]
    have hne1 : (1 : H →ₗ[ℂ] H) ≠ 0 := one_ne_zero
    have h4 : star z = z := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hne1)
    refine ⟨z.re, ?_⟩
    rw [Complex.conj_eq_iff_re.mp h4]
    exact e

end OneThing2

end Geometry

open Comparison.System.Geometry

/-- **Proposition 1 (the quaternionic structure).** For every system `H` with a quaternionic structure `Θ` (P1, P3 (a)): every
state is perpendicular to its conjugate and as long, `⟨v, Θv⟩ = 0`, `‖Θv‖ = ‖v‖`; in **every**
orthonormal basis `b` the quaternionic structure reads `Θv = J_b v̄` with `J_b` unitary and `J_bᵀ = −J_b`;
`Θ(iv) = −iΘv`; and there is a basis `u₁, −Θu₁, …, u_n, −Θu_n` in which the matrix of the quaternionic structure
is `J_n = diag(ε, …, ε)`, so `dim H = 2n`; in it the quaternions act (`i ↦ i·`, `j ↦ Θ`,
`k ↦ iΘ`, an algebra map) and the coordinates `ℍⁿ → H` are a bijection of `ℍ`-modules: `H = ℍⁿ`.
Recognition: none. -/
theorem prop_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : Partner H) :
    (∀ v : H, ⟪v, T.Θ v⟫_ℂ = 0 ∧ ‖T.Θ v‖ = ‖v‖) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ H),
      (∀ v i, ⟪b i, T.Θ v⟫_ℂ = (partnerMatrix T b *ᵥ star (fun j => ⟪b j, v⟫_ℂ)) i) ∧
      (partnerMatrix T b)ᴴ * partnerMatrix T b = 1 ∧
      (partnerMatrix T b)ᵀ = -partnerMatrix T b) ∧
    (∀ v : H, T.Θ (Complex.I • v) = -(Complex.I • T.Θ v)) ∧
    (∀ v : H, quatAction T ⟨0, 1, 0, 0⟩ v = Complex.I • v ∧ quatAction T ⟨0, 0, 1, 0⟩ v = T.Θ v ∧
      quatAction T ⟨0, 0, 0, 1⟩ v = Complex.I • T.Θ v) ∧
    ∃ n : ℕ, ∃ b : OrthonormalBasis (Fin n × Fin 2) ℂ H,
      (∀ k, b (k, 1) = -T.Θ (b (k, 0))) ∧ finrank ℂ H = 2 * n ∧ partnerMatrix T b = Jn n ∧
      Function.Bijective (quatCoords T (fun k => b (k, 0))) ∧
      ∀ (p : ℍ[ℝ]) (q : Fin n → ℍ[ℝ]), quatCoords T (fun k => b (k, 0)) (fun k => p * q k) =
        quatAction T p (quatCoords T (fun k => b (k, 0)) q) := by
  refine ⟨fun v => ⟨T.inner_self_Θ v, T.norm_Θ v⟩, fun b => ⟨partnerMatrix_coord T b,
    partnerMatrix_unitary T b, partnerMatrix_transpose T b⟩, fun v => ?_, fun v => ?_, ?_⟩
  · rw [T.map_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [quatAction_apply]
  · obtain ⟨n, b, hb⟩ := T.exists_normal_basis
    exact ⟨n, b, hb, Partner.finrank_eq b, partnerMatrix_normal T b hb, quatCoords_bijective T b hb,
      quatCoords_mul T _⟩

/-- **Proposition 2 (the distinctions).** For every system `(H, Θ)` with `dim H = 2n`, `n ≥ 1`, the
distinctions form a real space of dimension `2n² − n − 1`, isomorphic to `Herm₀(ℍⁿ)`, the Hermitian
`n × n` matrices of quaternions with trace zero. Recognition: none. -/
theorem prop_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : Partner H) {n : ℕ} (hn : 0 < n) (hdim : finrank ℂ H = 2 * n) :
    finrank ℝ (distinctionsH T) = 2 * n ^ 2 - n - 1 ∧
      Nonempty (distinctionsH T ≃ₗ[ℝ] hermZeroQ n) := by
  refine ⟨finrank_distinctionsH T hn hdim, ?_⟩
  obtain ⟨m, b, hb⟩ := T.exists_normal_basis
  have hm : m = n := by have := Partner.finrank_eq b; omega
  subst hm
  exact ⟨distinctionsH_equiv T b hb⟩

/-- **Proposition 3 (four amplitudes and five lines).** For every system `(H, Θ)`: some distinction is
not zero and every distinction squares to `τ(a²)·1` exactly when `dim H = 4`; then `dim Q = 5`. For a
candidate system this is the first two items of `System.uniqueness`. Recognition: none. -/
theorem prop_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : Partner H) :
    (((∃ a ∈ distinctionsH T, a ≠ 0) ∧
        ∀ a ∈ distinctionsH T, a * a = τH (a * a) • (1 : H →ₗ[ℂ] H)) ↔ finrank ℂ H = 4) ∧
      (finrank ℂ H = 4 → finrank ℝ (distinctionsH T) = 5) := by
  refine ⟨?_, fun h4 => ?_⟩
  · rw [← T.one_model_general, P3H_iff_tau]
    constructor
    · rintro ⟨⟨a, ha, h0⟩, h⟩
      exact ⟨⟨a, ha, h0⟩, fun a ha => h a ha⟩
    · rintro ⟨⟨a, ha, h0⟩, h⟩
      exact ⟨⟨a, ha, h0⟩, fun a ha => h a ha⟩
  · have := finrank_distinctionsH T (n := 2) (by norm_num) (by rw [h4])
    rw [this]
    norm_num

end Comparison.System
