import Comparison.System.Geometry.OneThing
import Comparison.Article.RealModel

/-!
# The geometry of comparison, Book III continued: the square root of the sign uses P1's `i` (Proposition 20)

With real numbers in P1 a system is a finite-dimensional real Hilbert space `H` and its conjugate an
orthogonal map `Θ` with `Θ² = −1` (`RealPartner`). Proved here for **every** such `(H, Θ)`:

* `RealPartner.inner_Θ_self`, `RealPartner.inner_Θ_left`: `⟨v, Θv⟩ = 0` and `Θᵀ = −Θ`: the quaternionic structure is
  a complex structure;
* `RealPartner.exists_normal_basis`: an orthonormal basis `v₁, Θv₁, …, v_m, Θv_m`, `dim H = 2m`;
* `RealPartner.P3R_iff`: P3 (b) over the reals (some distinction is not zero, every distinction —
  symmetric, of trace zero, commuting with `Θ` — squares to a number) holds **exactly when
  `dim H = 4`**, and then `dim Q = 3` (`RealPartner.finrank_Q`): the three Pauli matrices,
  `Q = Herm₀(ℂ²)`.

With the earlier theorems (`Article/RealModel.lean`): a real `q` with `q² = θ_D` has
`(det q)² = (−1)^{|D|}`; on `ℝ² ⊗ ℝ²` the products of symmetric operators span 9 of the 10 symmetric
operators, on `ℂ² ⊗ ℂ²` all 16.
-/

open scoped InnerProductSpace Kronecker
open Matrix Module

namespace Comparison.System

namespace Geometry

/-- **A quaternionic structure with real numbers in P1:** an orthogonal map with `Θ² = −1`. -/
structure RealPartner (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The quaternionic structure map. -/
  Θ : H →ₗ[ℝ] H
  inner_Θ : ∀ v w, ⟪Θ v, Θ w⟫_ℝ = ⟪v, w⟫_ℝ
  Θ_Θ : ∀ v, Θ (Θ v) = -v

namespace RealPartner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : RealPartner H)

/-- **No state is its own conjugate:** `⟨Θv, v⟩ = 0`. -/
theorem inner_Θ_self (v : H) : ⟪T.Θ v, v⟫_ℝ = 0 := by
  have h := T.inner_Θ v (T.Θ v)
  rw [T.Θ_Θ, inner_neg_right] at h
  have h2 : ⟪v, T.Θ v⟫_ℝ = ⟪T.Θ v, v⟫_ℝ := real_inner_comm _ _
  linarith

theorem inner_self_Θ (v : H) : ⟪v, T.Θ v⟫_ℝ = 0 := by
  rw [real_inner_comm]; exact T.inner_Θ_self v

/-- **The quaternionic structure is antisymmetric:** `⟨Θv, w⟩ = −⟨v, Θw⟩`. -/
theorem inner_Θ_left (v w : H) : ⟪T.Θ v, w⟫_ℝ = -⟪v, T.Θ w⟫_ℝ := by
  have h := T.inner_Θ (T.Θ v) w
  rw [T.Θ_Θ, inner_neg_left] at h
  linarith

theorem norm_Θ (v : H) : ‖T.Θ v‖ = ‖v‖ := by
  have h := T.inner_Θ v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

variable [FiniteDimensional ℝ H]

/-- **The pairs of a real structure.** Every subspace `K` kept by `Θ` has unit vectors
`u₁, …, u_m` in `K`, `u_k` perpendicular to `u_l` and to `Θu_l` for `k ≠ l`, with `2m = dim K`. -/
theorem exists_pairs (d : ℕ) : ∀ K : Submodule ℝ H, finrank ℝ K = d →
    (∀ x ∈ K, T.Θ x ∈ K) →
    ∃ m : ℕ, ∃ u : Fin m → H, (∀ k, u k ∈ K) ∧ (∀ k, ‖u k‖ = 1) ∧
      (∀ k l, k ≠ l → ⟪u k, u l⟫_ℝ = 0 ∧ ⟪u k, T.Θ (u l)⟫_ℝ = 0) ∧ 2 * m = d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K hd hK
  by_cases hK0 : K = ⊥
  · refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
    rw [← hd, hK0, finrank_bot]
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  set y : H := (‖x‖⁻¹) • x with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  have hyK : y ∈ K := K.smul_mem _ hxK
  have hΘyK : T.Θ y ∈ K := hK y hyK
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range ![y, T.Θ y]) with hS
  have hyS : y ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hΘyS : T.Θ y ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have hSK : S ≤ K := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hyK
    · exact hΘyK
  have horth : Orthonormal ℝ ![y, T.Θ y] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simp [real_inner_self_eq_norm_sq, hy1]
    · simp [T.inner_self_Θ]
    · simp [T.inner_Θ_self]
    · simp [real_inner_self_eq_norm_sq, T.norm_Θ, hy1]
  have hS2 : finrank ℝ S = 2 := by
    rw [hS, finrank_span_eq_card horth.linearIndependent]
    simp
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal hSK
  rw [hS2, hd] at hdim
  have memS : ∀ w, w ∈ Sᗮ ↔ ⟪y, w⟫_ℝ = 0 ∧ ⟪T.Θ y, w⟫_ℝ = 0 := by
    intro w
    constructor
    · intro hw
      exact ⟨(Submodule.mem_orthogonal S w).mp hw y hyS,
        (Submodule.mem_orthogonal S w).mp hw (T.Θ y) hΘyS⟩
    · rintro ⟨h1, h2⟩
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        fin_cases i
        · exact h1
        · exact h2
      | zero => exact inner_zero_left w
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  set K' : Submodule ℝ H := Sᗮ ⊓ K with hK'
  have hK'Θ : ∀ w ∈ K', T.Θ w ∈ K' := by
    intro w hw
    rw [hK', Submodule.mem_inf] at hw ⊢
    obtain ⟨hwS, hwK⟩ := hw
    rw [memS] at hwS ⊢
    refine ⟨⟨?_, ?_⟩, hK w hwK⟩
    · rw [real_inner_comm, T.inner_Θ_left, real_inner_comm, hwS.2]; simp
    · rw [T.inner_Θ, hwS.1]
  obtain ⟨m', u', hu'K, hu'1, hu'2, hm'⟩ :=
    ih (d - 2) (by omega) K' (by omega) hK'Θ
  have hu'S : ∀ k, ⟪y, u' k⟫_ℝ = 0 ∧ ⟪T.Θ y, u' k⟫_ℝ = 0 := fun k =>
    (memS (u' k)).mp (Submodule.mem_inf.mp (hu'K k)).1
  have hΘu'S : ∀ k, ⟪y, T.Θ (u' k)⟫_ℝ = 0 := fun k =>
    ((memS _).mp (Submodule.mem_inf.mp (hK'Θ _ (hu'K k))).1).1
  refine ⟨m' + 1, Fin.cons y u', ?_, ?_, ?_, by omega⟩
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact hyK
    · exact (Submodule.mem_inf.mp (hu'K k)).2
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact hy1
    · exact hu'1 k
  · intro k l hkl
    induction k using Fin.cases with
    | zero =>
      induction l using Fin.cases with
      | zero => exact absurd rfl hkl
      | succ l => exact ⟨(hu'S l).1, hΘu'S l⟩
    | succ k =>
      induction l using Fin.cases with
      | zero =>
        refine ⟨?_, ?_⟩
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [real_inner_comm, (hu'S k).1]
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [real_inner_comm, (hu'S k).2]
      | succ l =>
        simp only [Fin.cons_succ]
        exact hu'2 k l (fun h => hkl (by rw [h]))

/-- The family `u₁, Θu₁, …, u_m, Θu_m`. -/
def pairs {m : ℕ} (u : Fin m → H) : Fin m × Fin 2 → H := fun p => ![u p.1, T.Θ (u p.1)] p.2

omit [FiniteDimensional ℝ H] in
theorem pairs_orthonormal {m : ℕ} (u : Fin m → H) (h1 : ∀ k, ‖u k‖ = 1)
    (h2 : ∀ k l, k ≠ l → ⟪u k, u l⟫_ℝ = 0 ∧ ⟪u k, T.Θ (u l)⟫_ℝ = 0) :
    Orthonormal ℝ (T.pairs u) := by
  rw [orthonormal_iff_ite]
  rintro ⟨k, a⟩ ⟨l, b⟩
  by_cases hkl : k = l
  · subst hkl
    fin_cases a <;> fin_cases b
    · simp [pairs, real_inner_self_eq_norm_sq, h1 k]
    · simp [pairs, T.inner_self_Θ]
    · simp [pairs, T.inner_Θ_self]
    · simp [pairs, real_inner_self_eq_norm_sq, T.norm_Θ, h1 k]
  · obtain ⟨hA, hB⟩ := h2 k l hkl
    obtain ⟨hC, hD⟩ := h2 l k (Ne.symm hkl)
    have hB' : ⟪T.Θ (u k), u l⟫_ℝ = 0 := by rw [real_inner_comm, hD]
    have hE : ⟪T.Θ (u k), T.Θ (u l)⟫_ℝ = 0 := by rw [T.inner_Θ, hA]
    fin_cases a <;> fin_cases b <;> simp [pairs, hkl, hA, hB, hB', hE]

/-- **The normal form of a real structure:** an orthonormal basis `u₁, Θu₁, …, u_m, Θu_m`. -/
theorem exists_normal_basis :
    ∃ m : ℕ, ∃ b : OrthonormalBasis (Fin m × Fin 2) ℝ H, ∀ k, b (k, 1) = T.Θ (b (k, 0)) := by
  obtain ⟨m, u, -, h1, h2, hm⟩ :=
    T.exists_pairs (finrank ℝ (⊤ : Submodule ℝ H)) ⊤ rfl (fun x _ => Submodule.mem_top)
  have hon := T.pairs_orthonormal u h1 h2
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (T.pairs u)) := by
    have h := finrank_span_eq_card hon.linearIndependent
    rw [finrank_top] at hm
    have htop : Submodule.span ℝ (Set.range (T.pairs u)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h]; simp; omega)
    rw [htop]
  refine ⟨m, OrthonormalBasis.mk hon hsp, fun k => ?_⟩
  simp [pairs]

omit [FiniteDimensional ℝ H] in
theorem finrank_eq {m : ℕ} (b : OrthonormalBasis (Fin m × Fin 2) ℝ H) : finrank ℝ H = 2 * m := by
  rw [Module.finrank_eq_card_basis b.toBasis]
  simp [mul_comm]

/-! ## The distinctions over the reals -/

/-- A distinction of a real system: symmetric, of trace zero, commuting with the quaternionic structure. -/
def IsDistinctionR (a : H →ₗ[ℝ] H) : Prop :=
  IsSelfAdjoint a ∧ LinearMap.trace ℝ H a = 0 ∧ ∀ v, a (T.Θ v) = T.Θ (a v)

/-- P3 (b) over the reals. -/
def P3R : Prop :=
  (∃ a, T.IsDistinctionR a ∧ a ≠ 0) ∧
    ∀ a, T.IsDistinctionR a → ∃ c : ℝ, a * a = c • (1 : H →ₗ[ℝ] H)

end RealPartner

/-! ## The real model family `ℝ^{2m}` -/

/-- The quaternionic structure's matrix in a real normal basis: `Θ(e_{k0}) = e_{k1}`, `Θ(e_{k1}) = −e_{k0}`. -/
def epsR' : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The real join `1 ⊗ ε′` on `ℝ^{2m}`. -/
def realJn (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ := (1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ epsR'

/-- A distinction of the real model `ℝ^{2m}`. -/
def IsDistinctionRN (m : ℕ) (a : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) : Prop :=
  aᵀ = a ∧ a.trace = 0 ∧ a * realJn m = realJn m * a

/-- P3 (b) on the real model `ℝ^{2m}`. -/
def P3RN (m : ℕ) : Prop :=
  (∃ a, IsDistinctionRN m a ∧ a ≠ 0) ∧
    ∀ a, IsDistinctionRN m a → ∃ c : ℝ, a * a = c • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)

theorem not_P3RN_zero : ¬ P3RN 0 := by
  rintro ⟨⟨a, -, ha⟩, -⟩
  apply ha
  ext ⟨i, _⟩
  exact i.elim0

set_option linter.flexible false in
theorem distinctionRN_one_eq_zero (a : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℝ)
    (ha : IsDistinctionRN 1 a) : a = 0 := by
  obtain ⟨hT, htr, hJ⟩ := ha
  have e : ∀ i j, (a * realJn 1) i j = (realJn 1 * a) i j := fun i j => by rw [hJ]
  have h1 := e (0, 0) (0, 0)
  have h2 := e (0, 0) (0, 1)
  have h4 := congrFun (congrFun hT (0, 0)) (0, 1)
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, realJn, epsR'] at h1 h2 h4
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htr
  ext ⟨i, α⟩ ⟨j, β⟩
  fin_cases i
  fin_cases j
  fin_cases α <;> fin_cases β <;> simp <;> linarith

theorem not_P3RN_one : ¬ P3RN 1 := by
  rintro ⟨⟨a, ha, hne⟩, -⟩
  exact hne (distinctionRN_one_eq_zero a ha)

/-- The real diagonal `diag(1, −1, 0, …) ⊗ 1` on `ℝ^{2(m+3)}`. -/
noncomputable def diagWitnessR (m : ℕ) : Matrix (Fin (m + 3) × Fin 2) (Fin (m + 3) × Fin 2) ℝ :=
  Matrix.diagonal (fun i => diagEntries m i) ⊗ₖ 1

theorem diagWitnessR_isDistinction (m : ℕ) : IsDistinctionRN (m + 3) (diagWitnessR m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [diagWitnessR, ← Matrix.kroneckerMap_transpose, Matrix.diagonal_transpose,
      Matrix.transpose_one]
  · rw [diagWitnessR, trace_kronecker, Matrix.trace_diagonal, diagEntries_sum, zero_mul]
  · rw [diagWitnessR, realJn, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

theorem diagWitnessR_sq_ne (m : ℕ) (c : ℝ) :
    diagWitnessR m * diagWitnessR m ≠
      c • (1 : Matrix (Fin (m + 3) × Fin 2) (Fin (m + 3) × Fin 2) ℝ) := by
  intro h
  have h0 := congrFun (congrFun h (⟨0, by omega⟩, 0)) (⟨0, by omega⟩, 0)
  have h2 := congrFun (congrFun h (⟨2, by omega⟩, 0)) (⟨2, by omega⟩, 0)
  rw [diagWitnessR, ← mul_kronecker_mul] at h0 h2
  simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Matrix.mul_one, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, diagEntries_zero,
    diagEntries_two] at h0 h2
  norm_num at h0 h2
  rw [← h0] at h2
  norm_num at h2

theorem not_P3RN_of_three_le (m : ℕ) (hm : 3 ≤ m) : ¬ P3RN m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rintro ⟨-, hsq⟩
  obtain ⟨c, hc⟩ := hsq _ (diagWitnessR_isDistinction k)
  exact diagWitnessR_sq_ne k c hc

theorem realJn_two : realJn 2 = -Comparison.Article.realJ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [realJn, epsR', Comparison.Article.realJ, Comparison.Article.epsR, Matrix.one_apply]

theorem isDistinctionRN_two_iff (a : Matrix Four Four ℝ) :
    IsDistinctionRN 2 a ↔ a ∈ Comparison.Article.realQ := by
  rw [IsDistinctionRN, realJn_two, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  rfl

theorem P3RN_two : P3RN 2 := by
  refine ⟨⟨Comparison.Article.realLines 0, (isDistinctionRN_two_iff _).mpr
    (Comparison.Article.realLines_mem 0), ?_⟩, fun a ha => ?_⟩
  · intro h
    have := congrFun (congrFun h (0, 0)) (0, 0)
    simp [Comparison.Article.realLines, Comparison.Article.s3R] at this
  · have hmem := (isDistinctionRN_two_iff a).mp ha
    rw [Comparison.Article.realQ_eq_span, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨t, rfl⟩ := hmem
    refine ⟨∑ i, t i ^ 2, ?_⟩
    have hc := Comparison.Article.realLines_clifford
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have h00 := hc 0 0; have h11 := hc 1 1; have h22 := hc 2 2
    have h01 := hc 0 1; have h02 := hc 0 2; have h12 := hc 1 2
    simp only [ite_true, Fin.isValue] at h00 h11 h22
    simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide, ite_false, zero_smul] at h01 h02 h12
    have s0 : Comparison.Article.realLines 0 * Comparison.Article.realLines 0 = 1 := by
      have := h00; rw [← two_smul ℝ] at this; exact smul_right_injective _ two_ne_zero this
    have s1 : Comparison.Article.realLines 1 * Comparison.Article.realLines 1 = 1 := by
      have := h11; rw [← two_smul ℝ] at this; exact smul_right_injective _ two_ne_zero this
    have s2 : Comparison.Article.realLines 2 * Comparison.Article.realLines 2 = 1 := by
      have := h22; rw [← two_smul ℝ] at this; exact smul_right_injective _ two_ne_zero this
    have a10 : Comparison.Article.realLines 1 * Comparison.Article.realLines 0 =
        -(Comparison.Article.realLines 0 * Comparison.Article.realLines 1) :=
      eq_neg_of_add_eq_zero_right h01
    have a20 : Comparison.Article.realLines 2 * Comparison.Article.realLines 0 =
        -(Comparison.Article.realLines 0 * Comparison.Article.realLines 2) :=
      eq_neg_of_add_eq_zero_right h02
    have a21 : Comparison.Article.realLines 2 * Comparison.Article.realLines 1 =
        -(Comparison.Article.realLines 1 * Comparison.Article.realLines 2) :=
      eq_neg_of_add_eq_zero_right h12
    simp only [add_mul, mul_add, smul_mul_smul_comm, s0, s1, s2, a10, a20, a21]
    module

/-- **On the real model `ℝ^{2m}`, P3 (b) holds exactly when `m = 2`.** -/
theorem P3RN_iff (m : ℕ) : P3RN m ↔ m = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · exact absurd h not_P3RN_zero
      · exact absurd h not_P3RN_one
      · rfl
    · exact absurd h (not_P3RN_of_three_le m hm)
  · rintro rfl
    exact P3RN_two

/-! ## Every real system with a quaternionic structure: P3 (b) over the reals holds exactly when `dim H = 4` -/

namespace RealPartner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (T : RealPartner H)

/-- **In a real normal basis the quaternionic structure has the matrix `1 ⊗ ε′`.** -/
theorem matrix_Θ {m : ℕ} (b : OrthonormalBasis (Fin m × Fin 2) ℝ H)
    (hb : ∀ k, b (k, 1) = T.Θ (b (k, 0))) :
    LinearMap.toMatrixOrthonormal b T.Θ = realJn m := by
  have hΘ0 : ∀ l, T.Θ (b (l, 0)) = b (l, 1) := fun l => (hb l).symm
  have hΘ1 : ∀ l, T.Θ (b (l, 1)) = -b (l, 0) := fun l => by rw [hb l, T.Θ_Θ]
  ext ⟨k, α⟩ ⟨l, β⟩
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  fin_cases α <;> fin_cases β <;>
    simp [hΘ0, hΘ1, inner_neg_right, orthonormal_iff_ite.mp b.orthonormal, realJn, epsR',
      Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- **A distinction of `(H, Θ)` is a distinction of the real model in a normal basis.** -/
theorem isDistinctionR_iff {m : ℕ} (b : OrthonormalBasis (Fin m × Fin 2) ℝ H)
    (hb : ∀ k, b (k, 1) = T.Θ (b (k, 0))) (a : H →ₗ[ℝ] H) :
    T.IsDistinctionR a ↔ IsDistinctionRN m (LinearMap.toMatrixOrthonormal b a) := by
  have hsa : IsSelfAdjoint a ↔
      (LinearMap.toMatrixOrthonormal b a)ᵀ = LinearMap.toMatrixOrthonormal b a := by
    rw [IsSelfAdjoint, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← map_star]
    exact (LinearMap.toMatrixOrthonormal b).injective.eq_iff.symm
  have htr : LinearMap.trace ℝ H a = (LinearMap.toMatrixOrthonormal b a).trace := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
    rfl
  have hΘ : (∀ v, a (T.Θ v) = T.Θ (a v)) ↔
      LinearMap.toMatrixOrthonormal b a * realJn m = realJn m * LinearMap.toMatrixOrthonormal b a := by
    rw [← T.matrix_Θ b hb, ← map_mul, ← map_mul,
      (EquivLike.injective (LinearMap.toMatrixOrthonormal b)).eq_iff]
    constructor
    · intro h
      ext v
      exact h v
    · intro h v
      exact LinearMap.congr_fun h v
  rw [IsDistinctionR, IsDistinctionRN, hsa, htr, hΘ]

/-- **P3 (b) over the reals for `(H, Θ)` is P3 (b) for the real model of the same size.** -/
theorem P3R_iff_model {m : ℕ} (b : OrthonormalBasis (Fin m × Fin 2) ℝ H)
    (hb : ∀ k, b (k, 1) = T.Θ (b (k, 0))) : T.P3R ↔ P3RN m := by
  set e := LinearMap.toMatrixOrthonormal b with he
  have hsq : ∀ (a : H →ₗ[ℝ] H) (c : ℝ), a * a = c • (1 : H →ₗ[ℝ] H) ↔
      e a * e a = c • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) := by
    intro a c
    rw [← map_mul, ← map_one e, ← map_smul]
    exact e.injective.eq_iff.symm
  constructor
  · rintro ⟨⟨a, ha, ha0⟩, hall⟩
    refine ⟨⟨e a, (T.isDistinctionR_iff b hb a).mp ha, ?_⟩, fun M hM => ?_⟩
    · intro h0
      exact ha0 (e.injective (h0.trans (map_zero e).symm))
    · obtain ⟨a, rfl⟩ := e.surjective M
      obtain ⟨c, hc⟩ := hall a ((T.isDistinctionR_iff b hb a).mpr hM)
      exact ⟨c, (hsq a c).mp hc⟩
  · rintro ⟨⟨M, hM, hM0⟩, hall⟩
    obtain ⟨a, rfl⟩ := e.surjective M
    refine ⟨⟨a, (T.isDistinctionR_iff b hb a).mpr hM, ?_⟩, fun a' ha' => ?_⟩
    · intro h0
      exact hM0 (by rw [h0, map_zero])
    · obtain ⟨c, hc⟩ := hall (e a') ((T.isDistinctionR_iff b hb a').mp ha')
      exact ⟨c, (hsq a' c).mpr hc⟩

/-- **With real numbers in P1, P3 (b) holds exactly when `dim_ℝ H = 4`.** -/
theorem P3R_iff : T.P3R ↔ finrank ℝ H = 4 := by
  obtain ⟨m, b, hb⟩ := T.exists_normal_basis
  rw [T.P3R_iff_model b hb, P3RN_iff, RealPartner.finrank_eq b]
  constructor <;> intro h <;> omega

/-- The distinctions of a real system, a real vector space. -/
def distinctionsR : Submodule ℝ (H →ₗ[ℝ] H) where
  carrier := {a | T.IsDistinctionR a}
  add_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨ha1.add hb1, by rw [map_add, ha2, hb2, add_zero], fun v => ?_⟩
    simp only [LinearMap.add_apply, ha3, hb3, map_add]
  zero_mem' := ⟨IsSelfAdjoint.zero _, by simp, fun v => by simp⟩
  smul_mem' r a ha := by
    obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨(IsSelfAdjoint.all r).smul h1, by rw [map_smul, h2, smul_zero], fun v => ?_⟩
    simp only [LinearMap.smul_apply, h3, map_smul]

/-- **`dim Q = 3`** for every real system with a quaternionic structure and P3 (b): the three real lines. -/
theorem finrank_distinctionsR (h4 : finrank ℝ H = 4) : finrank ℝ T.distinctionsR = 3 := by
  obtain ⟨m, b, hb⟩ := T.exists_normal_basis
  have hm : m = 2 := by have := RealPartner.finrank_eq b; omega
  subst hm
  set e := (LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearEquiv with he
  have hmap : T.distinctionsR.map e.toLinearMap = Comparison.Article.realQ := by
    ext M
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (isDistinctionRN_two_iff _).mp ((T.isDistinctionR_iff b hb a).mp ha)
    · intro hM
      obtain ⟨a, rfl⟩ := e.surjective M
      exact ⟨a, (T.isDistinctionR_iff b hb a).mpr ((isDistinctionRN_two_iff _).mpr hM), rfl⟩
  rw [← Comparison.Article.finrank_realQ, ← hmap]
  exact (Submodule.equivMapOfInjective _ e.injective _).finrank_eq

end RealPartner

/-! ## `Q = Herm₀(ℂ²)` on the real model, and the ten symmetric operators -/

/-- **`Herm₀(ℂ²)`:** the Hermitian `2 × 2` complex matrices of trace zero. -/
def hermZero2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {M | Mᴴ = M ∧ M.trace = 0}
  add_mem' {M N} hM hN := ⟨by rw [Matrix.conjTranspose_add, hM.1, hN.1],
    by rw [Matrix.trace_add, hM.2, hN.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' r M hM := ⟨by rw [Matrix.conjTranspose_smul, hM.1, star_trivial],
    by rw [Matrix.trace_smul, hM.2, smul_zero]⟩

/-- The three Pauli matrices in the order of the three real lines. -/
def pauli3 : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![σ₃, σ₁, σ₂]

theorem pauli3_mem (i : Fin 3) : pauli3 i ∈ hermZero2 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;>
    first
    | (ext a b; fin_cases a <;> fin_cases b <;> simp [pauli3, σ₁, σ₂, σ₃])
    | simp [pauli3, σ₁, σ₂, σ₃, Matrix.trace, Fin.sum_univ_two]

theorem pauli3_clifford (i j : Fin 3) :
    pauli3 i * pauli3 j + pauli3 j * pauli3 i = (if i = j then (2 : ℂ) else 0) • 1 := by
  fin_cases i <;> fin_cases j <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
      simp [pauli3, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring_nf <;>
      simp [Complex.I_sq] <;> norm_num)

theorem hermZero2_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ hermZero2) :
    M = ((M 0 0).re : ℂ) • pauli3 0 + ((M 0 1).re : ℂ) • pauli3 1 - ((M 0 1).im : ℂ) • pauli3 2 := by
  obtain ⟨h1, h2⟩ := hM
  have e10 := congrFun (congrFun h1 1) 0
  have e00 := congrFun (congrFun h1 0) 0
  simp only [Matrix.conjTranspose_apply] at e10 e00
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag] at h2
  have i00 : (M 0 0).im = 0 := by
    have := congrArg Complex.im e00
    simp at this
    linarith
  have r11 : (M 1 1).re = -(M 0 0).re := by
    have := congrArg Complex.re h2
    simp at this
    linarith
  have i11 : (M 1 1).im = 0 := by
    have := congrArg Complex.im h2
    simp at this
    linarith
  have r10 : (M 1 0).re = (M 0 1).re := by
    have := congrArg Complex.re e10
    simp at this
    linarith
  have i10 : (M 1 0).im = -(M 0 1).im := by
    have := congrArg Complex.im e10
    simp at this
    linarith
  ext a b
  rw [Complex.ext_iff]
  fin_cases a <;> fin_cases b <;> constructor <;>
    simp [pauli3, σ₁, σ₂, σ₃] <;> linarith [i00, r11, i11, r10, i10]

theorem pauli3_linearIndependent : LinearIndependent ℝ pauli3 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e00 := congrFun (congrFun hg 0) 0
  have e01 := congrFun (congrFun hg 0) 1
  simp [Fin.sum_univ_three, pauli3, σ₁, σ₂, σ₃] at e00 e01
  have h01re := congrArg Complex.re e01
  have h01im := congrArg Complex.im e01
  simp at h01re h01im
  fin_cases i
  · exact_mod_cast e00
  · exact h01re
  · exact h01im

theorem hermZero2_span : hermZero2 = Submodule.span ℝ (Set.range pauli3) := by
  apply le_antisymm
  · intro M hM
    rw [hermZero2_eq M hM]
    refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      · rw [Complex.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact pauli3_mem i

/-- **`Q = Herm₀(ℂ²)` on the real model:** a real-linear isomorphism carrying the three real lines to
the three Pauli matrices. -/
noncomputable def realQEquivHerm : Comparison.Article.realQ ≃ₗ[ℝ] hermZero2 :=
  let b1 : Basis (Fin 3) ℝ Comparison.Article.realQ :=
    (Basis.span Comparison.Article.realLines_linearIndependent).map
      (LinearEquiv.ofEq _ _ Comparison.Article.realQ_eq_span.symm)
  let b2 : Basis (Fin 3) ℝ hermZero2 :=
    (Basis.span pauli3_linearIndependent).map (LinearEquiv.ofEq _ _ hermZero2_span.symm)
  b1.equiv b2 (Equiv.refl _)

theorem realQEquivHerm_lines (i : Fin 3) :
    (realQEquivHerm ⟨Comparison.Article.realLines i, Comparison.Article.realLines_mem i⟩ :
      Matrix (Fin 2) (Fin 2) ℂ) = pauli3 i := by
  simp only [realQEquivHerm]
  have h1 : (⟨Comparison.Article.realLines i, Comparison.Article.realLines_mem i⟩ :
      Comparison.Article.realQ) =
      ((Basis.span Comparison.Article.realLines_linearIndependent).map
        (LinearEquiv.ofEq _ _ Comparison.Article.realQ_eq_span.symm)) i := by
    ext1
    simp [Basis.span_apply]
  rw [h1, Basis.equiv_apply]
  simp [Basis.span_apply]

/-- The symmetric real `4 × 4` matrices. -/
def symFour : Submodule ℝ (Matrix Four Four ℝ) where
  carrier := {M | Mᵀ = M}
  add_mem' {M N} hM hN := by
    show (M + N)ᵀ = M + N
    rw [Matrix.transpose_add, hM, hN]
  zero_mem' := by
    show (0 : Matrix Four Four ℝ)ᵀ = 0
    simp
  smul_mem' r M hM := by
    show (r • M)ᵀ = r • M
    rw [Matrix.transpose_smul, hM]

/-- The coefficients of a symmetric `X` along the nine products. -/
noncomputable def symCoef (X : Matrix Four Four ℝ) : Fin 3 × Fin 3 → ℝ := fun p =>
  (![![X (0, 0) (0, 0), X (0, 1) (0, 1), X (0, 0) (0, 1)],
    ![X (1, 0) (1, 0), X (1, 1) (1, 1), X (1, 0) (1, 1)],
    ![X (0, 0) (1, 0), X (0, 1) (1, 1), (X (0, 0) (1, 1) + X (0, 1) (1, 0)) / 2]] :
      Fin 3 → Fin 3 → ℝ) p.1 p.2

theorem symFour_decomp (X : Matrix Four Four ℝ) (hX : X ∈ symFour) :
    X ∈ Submodule.span ℝ (Set.range Comparison.Article.realProducts) ⊔
      Submodule.span ℝ {Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR} := by
  have hs : ∀ p q, X q p = X p q := fun p q => by
    have := congrFun (congrFun hX p) q
    simpa using this
  have hdec : X = ∑ p, symCoef X p • Comparison.Article.realProducts p +
      ((X (0, 0) (1, 1) - X (0, 1) (1, 0)) / 2) •
        (Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR) := by
    ext ⟨a, b⟩ ⟨e, f⟩
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_three, Comparison.Article.realProducts,
      Matrix.kroneckerMap_apply, symCoef]
    fin_cases a <;> fin_cases b <;> fin_cases e <;> fin_cases f <;>
      simp [Comparison.Article.symR, Comparison.Article.epsR] <;>
      linarith [hs (0, 0) (0, 1), hs (0, 0) (1, 0), hs (0, 0) (1, 1), hs (0, 1) (1, 0),
        hs (0, 1) (1, 1), hs (1, 0) (1, 1)]
  rw [hdec]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span rfl)))

/-- **The symmetric operators of `ℝ² ⊗ ℝ²` have dimension ten.** -/
theorem finrank_symFour : finrank ℝ symFour = 10 := by
  have hle : Submodule.span ℝ (Set.range Comparison.Article.realProducts) ⊔
      Submodule.span ℝ {Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR} ≤ symFour := by
    apply sup_le
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Comparison.Article.realProducts_symm p
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Comparison.Article.realProducts_nine.2.1
  have heq : symFour = Submodule.span ℝ (Set.range Comparison.Article.realProducts) ⊔
      Submodule.span ℝ {Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR} :=
    le_antisymm (fun X hX => symFour_decomp X hX) hle
  have hdisj : Disjoint (Submodule.span ℝ (Set.range Comparison.Article.realProducts))
      (Submodule.span ℝ {Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR}) := by
    rw [Submodule.disjoint_span_singleton' (by
      intro h
      have := congrFun (congrFun h (0, 0)) (1, 1)
      simp [Comparison.Article.epsR] at this)]
    exact Comparison.Article.realProducts_nine.2.2.2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (Set.range Comparison.Article.realProducts))
    (Submodule.span ℝ {Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR})
  rw [hdisj.eq_bot, finrank_bot, add_zero, Comparison.Article.realProducts_nine.1,
    finrank_span_singleton (by
      intro h
      have := congrFun (congrFun h (0, 0)) (1, 1)
      simp [Comparison.Article.epsR] at this)] at hsum
  rw [heq, hsum]

/-- **`Q ≅ Herm₀(ℂ²)` for every real system with a quaternionic structure and `dim H = 4`:** the matrix in a normal
basis carries `Q` onto the model's, and the model's onto `Herm₀(ℂ²)`. -/
theorem RealPartner.distinctionsR_equiv_herm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (T : RealPartner H) (h4 : finrank ℝ H = 4) :
    Nonempty (T.distinctionsR ≃ₗ[ℝ] hermZero2) := by
  obtain ⟨m, b, hb⟩ := T.exists_normal_basis
  have hm : m = 2 := by have := RealPartner.finrank_eq b; omega
  subst hm
  set e := (LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearEquiv with he
  have hmap : T.distinctionsR.map e.toLinearMap = Comparison.Article.realQ := by
    ext M
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (isDistinctionRN_two_iff _).mp ((T.isDistinctionR_iff b hb a).mp ha)
    · intro hM
      obtain ⟨a, rfl⟩ := e.surjective M
      exact ⟨a, (T.isDistinctionR_iff b hb a).mpr ((isDistinctionRN_two_iff _).mpr hM), rfl⟩
  exact ⟨((Submodule.equivMapOfInjective _ e.injective _).trans
    (LinearEquiv.ofEq _ _ hmap)).trans realQEquivHerm⟩

end Geometry

open Comparison.System.Geometry

/-- **Proposition 20 (the square root of the sign uses P1's `i`).** With real numbers in P1 — a real Hilbert space `H`
with an orthogonal quaternionic structure, `Θ² = −1` — for **every** such `(H, Θ)`: `Θᵀ = −Θ`, P3 (b) holds exactly
when `dim H = 4`, and then `dim Q = 3`: on the real model `Q` is spanned by three lines that
anticommute and square to one, the two-spinor states of the three Pauli matrices (`Herm₀(ℂ²)`); with complex
P1, `i`, `Θ`, `iΘ` multiply as the quaternion units and `dim Q = 5`; a real `q` with `q² = −1` on
`k` directions and `+1` on the rest has `(det q)² = (−1)^k`, so `k` is even; the products of
symmetric operators on `ℝ² ⊗ ℝ²` span 9 dimensions and miss the symmetric `ε ⊗ ε`, while on
`ℂ² ⊗ ℂ²` they span all 16 Hermitian operators. Recognition: the complex numbers stay in P1, and the square
root of the sign of a division uses P1's `i`. -/
theorem prop_20 :
    (∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (T : RealPartner H),
      (∀ v w, ⟪T.Θ v, w⟫_ℝ = -⟪v, T.Θ w⟫_ℝ) ∧ (∀ v, T.Θ (T.Θ v) = -v) ∧
      (T.P3R ↔ finrank ℝ H = 4) ∧ (finrank ℝ H = 4 → finrank ℝ T.distinctionsR = 3) ∧
      (finrank ℝ H = 4 → Nonempty (T.distinctionsR ≃ₗ[ℝ] hermZero2))) ∧
    Comparison.Article.realQ = Submodule.span ℝ (Set.range Comparison.Article.realLines) ∧
    (∀ i j : Fin 3, Comparison.Article.realLines i * Comparison.Article.realLines j +
      Comparison.Article.realLines j * Comparison.Article.realLines i =
        (if i = j then 2 else 0 : ℝ) • 1) ∧
    finrank ℝ Comparison.Article.realQ = 3 ∧
    (∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
        (T : Partner H),
      (∀ v : H, T.Θ (T.Θ v) = -v) ∧ (∀ v : H, T.Θ (Complex.I • v) = -(Complex.I • T.Θ v)) ∧
      (finrank ℂ H = 4 → finrank ℝ (distinctionsH T) = 5)) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (q : Matrix n n ℝ) (D : Finset n),
      q * q = Matrix.diagonal (fun i => if i ∈ D then -1 else 1) →
        q.det ^ 2 = (-1) ^ D.card ∧ Even D.card) ∧
    (finrank ℝ (Submodule.span ℝ (Set.range Comparison.Article.realProducts)) = 9 ∧
      (Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR)ᵀ =
        Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR ∧
      (∀ p, ((Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR) *
        Comparison.Article.realProducts p).trace = 0) ∧
      Comparison.Article.epsR ⊗ₖ Comparison.Article.epsR ∉
        Submodule.span ℝ (Set.range Comparison.Article.realProducts)) ∧
    Submodule.span ℝ (Set.range fun p : Fin 4 × Fin 4 => pauli p.1 ⊗ₖ pauli p.2) = hermitian ∧
    (∀ i j : Fin 3, pauli3 i * pauli3 j + pauli3 j * pauli3 i = (if i = j then (2 : ℂ) else 0) • 1) ∧
    hermZero2 = Submodule.span ℝ (Set.range pauli3) ∧ LinearIndependent ℝ pauli3 ∧
    (∀ i : Fin 3, (realQEquivHerm ⟨Comparison.Article.realLines i,
      Comparison.Article.realLines_mem i⟩ : Matrix (Fin 2) (Fin 2) ℂ) = pauli3 i) ∧
    finrank ℝ symFour = 10 ∧
    Submodule.span ℝ (Set.range Comparison.Article.realProducts) ≤ symFour := by
  refine ⟨fun T => ⟨T.inner_Θ_left, T.Θ_Θ, T.P3R_iff, T.finrank_distinctionsR,
    T.distinctionsR_equiv_herm⟩,
    Comparison.Article.realQ_eq_span, Comparison.Article.realLines_clifford,
    Comparison.Article.finrank_realQ, fun T => ⟨T.Θ_Θ, fun v => ?_, fun h4 => ?_⟩,
    fun q D h => Comparison.Article.real_half_det q D h, Comparison.Article.realProducts_nine,
    Comparison.Article.complexProducts_all, pauli3_clifford, hermZero2_span,
    pauli3_linearIndependent, realQEquivHerm_lines, finrank_symFour, by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Comparison.Article.realProducts_symm p⟩
  · rw [T.map_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · have := finrank_distinctionsH T (n := 2) (by norm_num) (by rw [h4])
    rw [this]
    norm_num

end Comparison.System
