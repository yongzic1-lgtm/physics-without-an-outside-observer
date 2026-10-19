module

public import Comparison.Elements.OneThing

/-!
# Book I, continued: the sixteen observables and the five-dimensional space of distinctions

* `obs`: the sixteen observables `1`, `γ_s` (five), `i γ_s γ_t` (ten).
* `trace_obs_mul`: they are orthonormal for `τ(XY) = tr(XY)/4`.
* `span_obs_eq_hermitian`, `finrank_hermitian`: they are a real basis of the Hermitian matrices,
  `16 = 1 + 5 + 10`.
* `obs_mul_J`: the one and the five directions commute with the quaternionic structure, the ten anticommute.
* `eq_sum_coord`: every distinction is `Σ t_s γ_s` with real `t_s = τ(a γ_s)`;
  `distinction_iff`: the distinctions are exactly these sums.
* `distinction_sq`: every distinction squares to `|t|² · 1`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The normalized trace `τ(X) = tr X / 4`. -/
noncomputable def τ (X : Matrix Four Four ℂ) : ℂ := X.trace / 4

/-- The one and the three Pauli matrices. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, σ₁, σ₂, σ₃]

theorem pauli_conjTranspose (a : Fin 4) : (pauli a)ᴴ = pauli a := by
  fin_cases a <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, σ₁, σ₂, σ₃])

theorem trace_pauli_mul (a b : Fin 4) :
    (pauli a * pauli b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli, σ₁, σ₂, σ₃, Matrix.trace_fin_two] <;>
    norm_num

/-- The sixteen observables of a system: the one, the five directions and the ten `i γ_s γ_t`. -/
def obs : Fin 16 → Matrix Four Four ℂ :=
  ![1, γ 0, γ 1, γ 2, γ 3, γ 4,
    I • (γ 0 * γ 1), I • (γ 0 * γ 2), I • (γ 0 * γ 3), I • (γ 0 * γ 4),
    I • (γ 1 * γ 2), I • (γ 1 * γ 3), I • (γ 1 * γ 4),
    I • (γ 2 * γ 3), I • (γ 2 * γ 4), I • (γ 3 * γ 4)]

/-- Where the five directions sit among the sixteen. -/
def lineIdx : Fin 5 → Fin 16 := ![1, 2, 3, 4, 5]

theorem obs_lineIdx (s : Fin 5) : obs (lineIdx s) = γ s := by
  fin_cases s <;> rfl

/-- Each of the sixteen is `±` a product of two Pauli matrices. -/
def obsSign : Fin 16 → ℂ := ![1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1]
/-- The Pauli matrix of the first pair. -/
def obsA : Fin 16 → Fin 4 := ![0, 1, 3, 2, 2, 2, 2, 3, 3, 3, 1, 1, 1, 0, 0, 0]
/-- The Pauli matrix of the second pair. -/
def obsB : Fin 16 → Fin 4 := ![0, 0, 0, 1, 2, 3, 0, 1, 2, 3, 1, 2, 3, 3, 2, 1]

set_option maxHeartbeats 4000000 in
-- sixteen observables, each checked on all sixteen entries
theorem obs_eq_pauli (k : Fin 16) :
    obs k = obsSign k • (pauli (obsA k) ⊗ₖ pauli (obsB k)) := by
  fin_cases k <;>
  · four_ext <;>
      simp [obs, obsSign, obsA, obsB, pauli, γ, σ₁, σ₂, σ₃, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

/-- The sixteen observables are Hermitian. -/
theorem obs_conjTranspose (k : Fin 16) : (obs k)ᴴ = obs k := by
  rw [obs_eq_pauli, conjTranspose_smul, conjTranspose_kronecker, pauli_conjTranspose,
    pauli_conjTranspose]
  fin_cases k <;> simp [obsSign]

set_option maxHeartbeats 4000000 in
-- 256 pairs, each a product of two traces of 2 × 2 matrices
/-- The sixteen observables are orthonormal: `tr(X_k X_l) = 4 δ_kl`. -/
theorem trace_obs_mul (k l : Fin 16) : (obs k * obs l).trace = if k = l then 4 else 0 := by
  rw [obs_eq_pauli, obs_eq_pauli, Matrix.smul_mul, Matrix.mul_smul, ← mul_kronecker_mul,
    Matrix.trace_smul, Matrix.trace_smul, trace_kronecker, trace_pauli_mul, trace_pauli_mul]
  fin_cases k <;> fin_cases l <;> simp [obsSign, obsA, obsB] <;> norm_num

theorem obs_linearIndependent : LinearIndependent ℂ obs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (fun M => (M * obs l).trace) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    trace_obs_mul, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Matrix.zero_mul, Matrix.trace_zero] at h
  simpa using h

/-- The sixteen observables are linearly independent over the real numbers. -/
theorem obs_linearIndependent_real : LinearIndependent ℝ obs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (fun M => (M * obs l).trace) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    trace_obs_mul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Matrix.zero_mul, Matrix.trace_zero] at h
  have h' := congrArg Complex.re h
  simpa using h'

/-- The sixteen observables span all `4 × 4` matrices over `ℂ`. -/
theorem obs_span : Submodule.span ℂ (Set.range obs) = ⊤ :=
  obs_linearIndependent.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])

/-- Every matrix is `Σ_k τ(X X_k) X_k`. -/
theorem expand (X : Matrix Four Four ℂ) : X = ∑ k, τ (X * obs k) • obs k := by
  have hX : X ∈ Submodule.span ℂ (Set.range obs) := obs_span ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, hc⟩ := hX
  have key : ∀ l, τ (X * obs l) = c l := by
    intro l
    rw [← hc]
    simp only [τ, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      trace_obs_mul, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  conv_lhs => rw [← hc]
  exact Finset.sum_congr rfl fun k _ => by rw [key]

theorem eq_zero_of_trace (B : Matrix Four Four ℂ) (h : ∀ k, (B * obs k).trace = 0) : B = 0 := by
  rw [expand B]
  simp [τ, h]

theorem star_trace_mul_of_hermitian {X Y : Matrix Four Four ℂ} (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    star (X * Y).trace = (X * Y).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, Matrix.trace_mul_comm]

/-- The trace of a product of two Hermitian matrices is real. -/
theorem trace_mul_re_of_hermitian {X Y : Matrix Four Four ℂ} (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    (((X * Y).trace.re : ℝ) : ℂ) = (X * Y).trace :=
  Complex.conj_eq_iff_re.mp (star_trace_mul_of_hermitian hX hY)

/-- `τ(XY)` is real for Hermitian `X` and `Y`. -/
theorem τ_re_of_hermitian {X Y : Matrix Four Four ℂ} (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    (((τ (X * Y)).re : ℝ) : ℂ) = τ (X * Y) := by
  apply Complex.conj_eq_iff_re.mp
  change star (τ (X * Y)) = τ (X * Y)
  rw [τ, star_div₀, star_trace_mul_of_hermitian hX hY]
  norm_num

/-- The Hermitian matrices, a real vector space. -/
def hermitian : Submodule ℝ (Matrix Four Four ℂ) where
  carrier := {X | Xᴴ = X}
  add_mem' := fun {X Y} (hX : Xᴴ = X) (hY : Yᴴ = Y) =>
    show (X + Y)ᴴ = X + Y by rw [Matrix.conjTranspose_add, hX, hY]
  zero_mem' := show (0 : Matrix Four Four ℂ)ᴴ = 0 by simp
  smul_mem' := fun r X (hX : Xᴴ = X) =>
    show (r • X)ᴴ = r • X by rw [Matrix.conjTranspose_smul, hX, star_trivial]

/-- Every Hermitian matrix is a real combination of the sixteen, with coefficients `τ(X X_k)`. -/
theorem hermitian_expand (X : Matrix Four Four ℂ) (hX : Xᴴ = X) :
    X = ∑ k, (((τ (X * obs k)).re : ℝ) : ℂ) • obs k := by
  conv_lhs => rw [expand X]
  exact Finset.sum_congr rfl fun k _ => by rw [τ_re_of_hermitian hX (obs_conjTranspose k)]

/-- **16 = 1 + 5 + 10.** The one, the five directions and the ten `i γ_s γ_t` span exactly the
Hermitian matrices over the real numbers. -/
theorem span_obs_eq_hermitian : Submodule.span ℝ (Set.range obs) = hermitian := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact obs_conjTranspose k
  · intro X hX
    rw [hermitian_expand X hX]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Complex.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The Hermitian `4 × 4` matrices form a real space of dimension `16 = 1 + 5 + 10`. -/
theorem finrank_hermitian : Module.finrank ℝ hermitian = 16 := by
  rw [← span_obs_eq_hermitian, finrank_span_eq_card obs_linearIndependent_real]
  simp

/-! ## The quaternionic structure on the sixteen -/

/-- `+1` on the one and the five directions, `-1` on the ten `i γ_s γ_t`. -/
def obsParity : Fin 16 → ℂ := ![1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

set_option maxHeartbeats 4000000 in
-- sixteen observables, each checked on all sixteen entries
/-- The one and the five directions commute with the quaternionic structure (`X J = J X̄`); the ten `i γ_s γ_t`
anticommute with it (`X J = -J X̄`). -/
theorem obs_mul_J (k : Fin 16) : obs k * J = obsParity k • (J * (obs k).map star) := by
  rw [obs_eq_pauli]
  fin_cases k <;>
  · four_ext <;>
      simp [obsParity, obsSign, obsA, obsB, pauli, σ₁, σ₂, σ₃, J, ε, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem map_star_mul (A B : Matrix Four Four ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

theorem trace_map_star (A : Matrix Four Four ℂ) : (A.map star).trace = star A.trace := by
  simp [Matrix.trace, star_sum]

theorem J_conjTranspose_mul : Jᴴ * J = 1 := by
  rw [J_conjTranspose, Matrix.neg_mul, J_mul_J, neg_neg]

/-- A distinction has no component along the ten `i γ_s γ_t`. -/
theorem trace_mul_obs_eq_zero {a : Matrix Four Four ℂ} (ha : IsDistinction a) {k : Fin 16}
    (hk : obsParity k = -1) : (a * obs k).trace = 0 := by
  obtain ⟨hH, -, hJ⟩ := ha
  have hO := obs_mul_J k
  rw [hk, neg_one_smul] at hO
  have hreal := star_trace_mul_of_hermitian hH (obs_conjTranspose k)
  have key : (a * obs k).trace = -star (a * obs k).trace := by
    calc (a * obs k).trace = (Jᴴ * (a * obs k * J)).trace := by
          rw [Matrix.trace_mul_comm Jᴴ, Matrix.mul_assoc (a * obs k) J Jᴴ, J_mul_conjTranspose,
            Matrix.mul_one]
      _ = (Jᴴ * -(J * (a * obs k).map star)).trace := by
          rw [Matrix.mul_assoc a, hO, Matrix.mul_neg, ← Matrix.mul_assoc, hJ,
            Matrix.mul_assoc, ← map_star_mul]
      _ = -star (a * obs k).trace := by
          rw [Matrix.mul_neg, ← Matrix.mul_assoc, J_conjTranspose_mul, Matrix.one_mul,
            Matrix.trace_neg, trace_map_star]
  rw [hreal] at key
  have h2 : (2 : ℂ) * (a * obs k).trace = 0 := by linear_combination key
  simpa using h2

/-! ## The distinctions are the real span of the five directions -/

/-- The coordinates of a matrix along the five directions: `t_s = Re τ(a γ_s)`. -/
noncomputable def coord (a : Matrix Four Four ℂ) (s : Fin 5) : ℝ := (τ (a * γ s)).re

theorem trace_γ_mul_obs (s : Fin 5) (k : Fin 16) :
    (γ s * obs k).trace = if lineIdx s = k then 4 else 0 := by
  rw [← obs_lineIdx, trace_obs_mul]

/-- **Every distinction is `Σ t_s γ_s`** with real `t_s = τ(a γ_s)`. -/
theorem eq_sum_coord (a : Matrix Four Four ℂ) (ha : IsDistinction a) :
    a = ∑ s, (coord a s : ℂ) • γ s := by
  have hre : ∀ s, ((coord a s : ℝ) : ℂ) = τ (a * γ s) := fun s =>
    τ_re_of_hermitian ha.1 (γ_conjTranspose s)
  have tri : ∀ k : Fin 16, k = 0 ∨ (∃ u, k = lineIdx u) ∨ obsParity k = -1 := by
    intro k
    fin_cases k
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨0, rfl⟩)
      | exact Or.inr (Or.inl ⟨1, rfl⟩)
      | exact Or.inr (Or.inl ⟨2, rfl⟩)
      | exact Or.inr (Or.inl ⟨3, rfl⟩)
      | exact Or.inr (Or.inl ⟨4, rfl⟩)
      | exact Or.inr (Or.inr (by simp [obsParity]))
  have hlineIdx : ∀ s u, lineIdx s = lineIdx u ↔ s = u := by decide
  have hpar : ∀ s, obsParity (lineIdx s) = 1 := by
    intro s; fin_cases s <;> simp [lineIdx, obsParity]
  apply sub_eq_zero.mp
  apply eq_zero_of_trace
  intro k
  simp only [Matrix.sub_mul, Matrix.trace_sub, Finset.sum_mul, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, trace_γ_mul_obs, smul_eq_mul, hre]
  rcases tri k with rfl | ⟨u, rfl⟩ | hk
  · have h0 : ∀ s, lineIdx s ≠ 0 := by decide
    simp [obs, ha.2.1, h0]
  · simp only [hlineIdx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      obs_lineIdx, τ]
    ring
  · have hne : ∀ s, lineIdx s ≠ k := by
      intro s h
      rw [← h, hpar] at hk
      norm_num at hk
    simp [trace_mul_obs_eq_zero ha hk, hne]

/-- Any real combination of the five directions is a distinction. -/
theorem sum_isDistinction (t : Fin 5 → ℝ) : IsDistinction (∑ s, (t s : ℂ) • γ s) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, γ_conjTranspose]
  · simp [Matrix.trace_sum, Matrix.trace_smul, γ_trace]
  · have hmap : (∑ s, (t s : ℂ) • γ s).map star = ∑ s, (t s : ℂ) • (γ s).map star := by
      ext i j
      simp [Matrix.sum_apply]
    rw [hmap, Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, γ_mul_J]

/-- **The distinctions are exactly the real combinations of the five directions.** -/
theorem distinction_iff (a : Matrix Four Four ℂ) :
    IsDistinction a ↔ ∃ t : Fin 5 → ℝ, a = ∑ s, (t s : ℂ) • γ s :=
  ⟨fun ha => ⟨coord a, eq_sum_coord a ha⟩, fun ⟨t, ht⟩ => ht ▸ sum_isDistinction t⟩

/-- The coordinates of `Σ t_s γ_s` are `t`: the five directions are a basis of the distinctions. -/
theorem coord_sum (t : Fin 5 → ℝ) : coord (∑ s, (t s : ℂ) • γ s) = t := by
  funext u
  simp only [coord, τ, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    ← obs_lineIdx, trace_obs_mul, smul_eq_mul]
  fin_cases u <;> simp [lineIdx, Fin.sum_univ_five]

/-- **The square of a combination of the five directions is `|t|² · 1`** (Clifford). -/
theorem sq_sum (t : Fin 5 → ℂ) :
    (∑ s, t s • γ s) * (∑ s, t s • γ s) = (∑ s, t s ^ 2) • (1 : Matrix Four Four ℂ) := by
  have h10 : γ 1 * γ 0 = -(γ 0 * γ 1) := γ_anticomm (by decide)
  have h20 : γ 2 * γ 0 = -(γ 0 * γ 2) := γ_anticomm (by decide)
  have h30 : γ 3 * γ 0 = -(γ 0 * γ 3) := γ_anticomm (by decide)
  have h40 : γ 4 * γ 0 = -(γ 0 * γ 4) := γ_anticomm (by decide)
  have h21 : γ 2 * γ 1 = -(γ 1 * γ 2) := γ_anticomm (by decide)
  have h31 : γ 3 * γ 1 = -(γ 1 * γ 3) := γ_anticomm (by decide)
  have h41 : γ 4 * γ 1 = -(γ 1 * γ 4) := γ_anticomm (by decide)
  have h32 : γ 3 * γ 2 = -(γ 2 * γ 3) := γ_anticomm (by decide)
  have h42 : γ 4 * γ 2 = -(γ 2 * γ 4) := γ_anticomm (by decide)
  have h43 : γ 4 * γ 3 = -(γ 3 * γ 4) := γ_anticomm (by decide)
  simp only [Fin.sum_univ_five, add_mul, mul_add, smul_mul_smul_comm, γ_mul_self,
    h10, h20, h30, h40, h21, h31, h41, h32, h42, h43]
  module

/-- **Every distinction squares to a number:** `a² = |t|² · 1` with `t` its coordinates. -/
theorem distinction_sq (a : Matrix Four Four ℂ) (ha : IsDistinction a) :
    a * a = ((∑ s, coord a s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [eq_sum_coord a ha, sq_sum, coord_sum]
  push_cast
  rfl

/-- Some distinction is not zero, and every distinction squares to a real number. -/
theorem P3_holds : (∃ a, IsDistinction a ∧ a ≠ 0) ∧
    ∀ a, IsDistinction a → ∃ c : ℝ, a * a = (c : ℂ) • (1 : Matrix Four Four ℂ) := by
  refine ⟨⟨γ 0, γ_isDistinction 0, ?_⟩, fun a ha => ⟨_, distinction_sq a ha⟩⟩
  intro h
  have := congrFun (congrFun h (0, 0)) (1, 0)
  simp [γ, σ₁] at this

end Comparison

end
