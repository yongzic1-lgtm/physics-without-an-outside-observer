module

public import Comparison.Elements.Observables

/-!
# The Elements of Comparison in Lean. Book II: two systems

Two systems have sixteen amplitudes, indexed by `Two = Four × Four`. A two-spinor state is a vector
`v : Two → ℂ`; `relOf M` is the two-spinor state `Σ M_xy u_x ⊗ u_y` with matrix `M`, and
`(A ⊗ B) (relOf M) = relOf (A M Bᵀ)` (`kron_mulVec_relOf`).

* `Ω`, the singlet: `Ω = ½ Σ_j u_j ⊗ Θ u_j` (`Ω_eq_sum`, the same in every orthonormal basis,
  `Ω_basis_free`), with matrix `M_Ω = -½ J`.
* `swap`, the swap; `Eop = 4 |Ω⟩⟨Ω|`; `L = 1 ⊗ 1 + Σ_s γ_s ⊗ γ_s`, the comparison.
* `L_eq_swap_singlet`: `L = 2 (swap + Eop)`.
* `rel k`, the sixteen two-spinor states `(B_k ⊗ 1) Ω` with `B_k = 1, γ_s, γ_s γ_t`; `disagreeSet k`
  the lines on which they disagree; `agreement`: `(γ_u ⊗ γ_u) e = ∓ e`;
  `L_rel`: `L e = (6 - 2 |S|) e`; `rel_inner`: orthonormal.
* `finrank_eigenspace_L_six/two/neg_two`: the values `6, 2, -2` with multiplicities
  `1, 10, 5`, and `eigenspace_L_other`: no other value.
* `disagreement_eq_zero_iff`: the singlet is the only two-spinor state with no disagreement.
* `disagreement_sum_sq`: `6 - L = ½ Σ_s (γ_s ⊗ 1 - 1 ⊗ γ_s)²`.
* `lineOf_unit`: the line of a unit state is a unit vector (Prop. 8).
* `disagreement_prodRel_ge`: every product state `a ⊗ b` disagrees by at least `4`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- Two systems: sixteen amplitudes. -/
abbrev Two := Four × Four

/-! ## Two-spinor states as matrices -/

/-- The two-spinor state with matrix `M`: `Σ M_xy u_x ⊗ u_y`. -/
def relOf (M : Matrix Four Four ℂ) : Two → ℂ := fun p => M p.1 p.2

/-- A sum over two systems is a double sum, one system at a time. -/
theorem sum_two (f : Two → ℂ) : ∑ p, f p = ∑ x : Four, ∑ y : Four, f (x, y) :=
  Fintype.sum_prod_type f

theorem relOf_injective : Function.Injective relOf := by
  intro M N h
  ext x y
  exact congrFun h (x, y)

theorem relOf_add (M N : Matrix Four Four ℂ) : relOf (M + N) = relOf M + relOf N := rfl

theorem relOf_smul (c : ℂ) (M : Matrix Four Four ℂ) : relOf (c • M) = c • relOf M := rfl

/-- `(A ⊗ B)` acts on the matrix of a two-spinor state as `M ↦ A M Bᵀ`. -/
theorem kron_mulVec_relOf (A B M : Matrix Four Four ℂ) :
    (A ⊗ₖ B) *ᵥ relOf M = relOf (A * M * Bᵀ) := by
  ext ⟨x, y⟩
  simp only [relOf, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.transpose_apply, sum_two, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- The inner product of two two-spinor states is `tr(M† N)`. -/
theorem dot_relOf (M N : Matrix Four Four ℂ) :
    star (relOf M) ⬝ᵥ relOf N = (Mᴴ * N).trace := by
  simp only [relOf, dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, sum_two]
  rw [Finset.sum_comm]

/-! ## The singlet -/

/-- The matrix of the singlet, `M_Ω = -½ J`. -/
noncomputable def MΩ : Matrix Four Four ℂ := (-(1 / 2) : ℂ) • J

/-- **The singlet** `Ω`, the two-spinor state in which every state is paired with its conjugate. -/
noncomputable def Ω : Two → ℂ := relOf MΩ

/-- `Ω = ½ Σ_j u_j ⊗ Θ u_j` for the standard basis `u_j`. -/
theorem Ω_eq_sum :
    Ω = (1 / 2 : ℂ) • ∑ j : Four, fun p : Two =>
      (Pi.single j (1 : ℂ) : Four → ℂ) p.1 * Θ (Pi.single j 1) p.2 := by
  ext ⟨x, y⟩
  have hJ : J y x = -J x y := by
    have := congrFun (congrFun J_transpose x) y
    simpa using this
  simp [Ω, relOf, MΩ, Θ, Matrix.mulVec, dotProduct, Pi.single_apply, hJ]

/-- The singlet is the same in every orthonormal basis: for every unitary `U` with columns `u_j`,
`½ Σ_j u_j ⊗ Θ u_j = Ω`. -/
theorem Ω_basis_free (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) :
    (1 / 2 : ℂ) • ∑ j : Four, (fun p : Two => U p.1 j * Θ (fun i => U i j) p.2) = Ω := by
  ext ⟨x, y⟩
  have hJ : J y x = -J x y := by
    have := congrFun (congrFun J_transpose x) y
    simpa using this
  have hUU : ∀ k, ∑ j, U x j * star (U k j) = if x = k then 1 else 0 := by
    intro k
    have := congrFun (congrFun hU x) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc ((1 / 2 : ℂ) • ∑ j : Four, (fun p : Two => U p.1 j * Θ (fun i => U i j) p.2)) (x, y)
      = (1 / 2) * ∑ k, J y k * ∑ j, U x j * star (U k j) := by
        simp only [Pi.smul_apply, Finset.sum_apply, Θ, Matrix.mulVec, dotProduct,
          Pi.star_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = (1 / 2) * J y x := by
        simp only [hUU, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]
    _ = Ω (x, y) := by
        simp only [Ω, relOf, MΩ, Matrix.smul_apply, smul_eq_mul, hJ]
        ring

theorem MΩ_mul_conjTranspose : MΩ * MΩᴴ = (1 / 4 : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [MΩ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, J_mul_conjTranspose,
    smul_smul]
  norm_num

/-- The singlet has length one. -/
theorem Ω_norm : star Ω ⬝ᵥ Ω = 1 := by
  rw [Ω, dot_relOf, Matrix.trace_mul_comm, MΩ_mul_conjTranspose, Matrix.trace_smul,
    Matrix.trace_one]
  norm_num

/-- For a Hermitian matrix, `ā = aᵀ`. -/
theorem map_star_eq_transpose {a : Matrix Four Four ℂ} (ha : aᴴ = a) : a.map star = aᵀ := by
  ext i j
  have := congrFun (congrFun ha j) i
  simp only [Matrix.conjTranspose_apply] at this
  simp [← this]

theorem γ_mul_J_eq (s : Fin 5) : γ s * J = J * (γ s)ᵀ := by
  rw [γ_mul_J, map_star_eq_transpose (γ_conjTranspose s)]

/-- On the matrix of the singlet: `M_Ω γ_sᵀ = γ_s M_Ω`. -/
theorem MΩ_mul_γ_transpose (s : Fin 5) : MΩ * (γ s)ᵀ = γ s * MΩ := by
  rw [MΩ, Matrix.smul_mul, Matrix.mul_smul, γ_mul_J_eq]

/-- **A line acts on the singlet the same from either system:** `(1 ⊗ γ_s) Ω = (γ_s ⊗ 1) Ω`. -/
theorem same_from_either_thing (s : Fin 5) : (1 ⊗ₖ γ s) *ᵥ Ω = (γ s ⊗ₖ 1) *ᵥ Ω := by
  rw [Ω, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, MΩ_mul_γ_transpose]

/-! ## The swap, `E` and the comparison -/

/-- The swap of the two systems. -/
def swap : Matrix Two Two ℂ := Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- `E = 4 |Ω⟩⟨Ω|`. -/
noncomputable def Eop : Matrix Two Two ℂ := Matrix.of fun p q => 4 * Ω p * star (Ω q)

/-- **The comparison** `L = 1 ⊗ 1 + Σ_s γ_s ⊗ γ_s`. -/
def L : Matrix Two Two ℂ := 1 ⊗ₖ 1 + ∑ s, γ s ⊗ₖ γ s

theorem swap_relOf (M : Matrix Four Four ℂ) : swap *ᵥ relOf M = relOf Mᵀ := by
  ext ⟨x, y⟩
  simp [swap, relOf, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_and]

set_option maxHeartbeats 8000000 in
-- 256 entries of a 16 × 16 identity
/-- **The comparison is the swap and the singlet:** `L = 2 (P + E)`. -/
theorem L_eq_swap_singlet : L = (2 : ℂ) • (swap + Eop) := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨e, f⟩, ⟨g, h⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;>
    simp [L, swap, Eop, Ω, relOf, MΩ, J, ε, γ, σ₁, σ₂, σ₃, Fin.sum_univ_five,
      Matrix.one_apply, RCLike.conj_ofNat] <;> norm_num

/-! ## The sixteen two-spinor states -/

/-- The operators that make the sixteen two-spinor states from the singlet: the one, the five directions and
the ten symmetric states `γ_s γ_t`. -/
def relOp : Fin 16 → Matrix Four Four ℂ :=
  ![1, γ 0, γ 1, γ 2, γ 3, γ 4,
    γ 0 * γ 1, γ 0 * γ 2, γ 0 * γ 3, γ 0 * γ 4, γ 1 * γ 2, γ 1 * γ 3, γ 1 * γ 4,
    γ 2 * γ 3, γ 2 * γ 4, γ 3 * γ 4]

/-- The lines on which each two-spinor state disagrees: none for the singlet, the four other lines for a
vector state, the two lines of a plane. -/
def disagreeSet : Fin 16 → Finset (Fin 5) :=
  ![∅, {1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3},
    {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

/-- **The sixteen two-spinor states** `(B_k ⊗ 1) Ω`: the singlet (`k = 0`), the five vector states
`ℓ_t = (γ_t ⊗ 1) Ω` (`k = 1, …, 5`) and the ten symmetric states `(γ_s γ_t ⊗ 1) Ω` (`k = 6, …, 15`). -/
noncomputable def rel (k : Fin 16) : Two → ℂ := (relOp k ⊗ₖ 1) *ᵥ Ω

theorem rel_eq_relOf (k : Fin 16) : rel k = relOf (relOp k * MΩ) := by
  rw [rel, Ω, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one]

theorem rel_zero : rel 0 = Ω := by
  rw [rel_eq_relOf]
  simp [relOp, Ω]

theorem γ_conj_line_ne {u s : Fin 5} (h : u ≠ s) : γ u * γ s * γ u = -γ s := by
  rw [γ_anticomm h, neg_mul, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]

theorem γ_conj_plane_left {s t : Fin 5} (h : s ≠ t) :
    γ s * (γ s * γ t) * γ s = -(γ s * γ t) := by
  rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul, γ_anticomm h.symm]

theorem γ_conj_plane_right {s t : Fin 5} (h : s ≠ t) :
    γ t * (γ s * γ t) * γ t = -(γ s * γ t) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one, γ_anticomm h.symm]

theorem γ_conj_plane_out {u s t : Fin 5} (hs : u ≠ s) (ht : u ≠ t) :
    γ u * (γ s * γ t) * γ u = γ s * γ t := by
  calc γ u * (γ s * γ t) * γ u = (γ u * γ s) * (γ t * γ u) := by
        simp only [Matrix.mul_assoc]
    _ = (-(γ s * γ u)) * (-(γ u * γ t)) := by rw [γ_anticomm hs, γ_anticomm (Ne.symm ht)]
    _ = γ s * (γ u * γ u) * γ t := by
        simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    _ = γ s * γ t := by rw [γ_mul_self, Matrix.mul_one]

/-- A line `γ_u` turns `B_k` into `∓ B_k`: minus exactly when the two-spinor state disagrees on `u`. -/
theorem γ_conj_relOp (u : Fin 5) (k : Fin 16) :
    γ u * relOp k * γ u = (if u ∈ disagreeSet k then -1 else 1 : ℂ) • relOp k := by
  fin_cases k <;> fin_cases u <;>
    simp [relOp, disagreeSet, γ_mul_self, γ_conj_line_ne, γ_conj_plane_left,
      γ_conj_plane_right, γ_conj_plane_out]

/-- **Agreement and disagreement:** `γ_u ⊗ γ_u` is `-1` on a two-spinor state that disagrees on `u` and
`+1` on one that agrees on it. -/
theorem agreement (u : Fin 5) (k : Fin 16) :
    (γ u ⊗ₖ γ u) *ᵥ rel k = (if u ∈ disagreeSet k then -1 else 1 : ℂ) • rel k := by
  rw [rel_eq_relOf, kron_mulVec_relOf]
  simp only [Matrix.mul_assoc]
  rw [MΩ_mul_γ_transpose]
  simp only [← Matrix.mul_assoc]
  rw [γ_conj_relOp, Matrix.smul_mul, relOf_smul]

/-- The count of disagreement on the line `u`: `n_u = (1 - γ_u ⊗ γ_u) / 2`. -/
noncomputable def count (u : Fin 5) : Matrix Two Two ℂ := (1 / 2 : ℂ) • (1 - γ u ⊗ₖ γ u)

/-- `n_u e = [u ∈ S] e`: the two-spinor state `e` disagrees exactly on the lines of `S`. -/
theorem count_rel (u : Fin 5) (k : Fin 16) :
    count u *ᵥ rel k = (if u ∈ disagreeSet k then 1 else 0 : ℂ) • rel k := by
  rw [count, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, agreement]
  split_ifs <;> module

theorem sum_sign (D : Finset (Fin 5)) :
    ∑ u : Fin 5, (if u ∈ D then -1 else 1 : ℂ) = 5 - 2 * D.card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have h : (Finset.univ.filter fun u : Fin 5 => u ∉ D).card = 5 - D.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ, Fintype.card_fin]
  rw [h]
  have hD : D.card ≤ 5 := by
    simpa using Finset.card_le_univ D
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  rw [Nat.cast_sub hD]
  push_cast
  ring

/-- **The comparison on the sixteen two-spinor states:** `L e = (1 + agree − disagree) e = (6 − 2|S|) e`. -/
theorem L_rel (k : Fin 16) :
    L *ᵥ rel k = ((6 : ℂ) - 2 * (disagreeSet k).card) • rel k := by
  rw [L, Matrix.add_mulVec, one_kronecker_one, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp only [agreement]
  rw [← Finset.sum_smul, sum_sign]
  module

/-- The two-spinor state `e_k` has the matrix `B_k M_Ω`; up to a phase `B_k` is the observable `X_k`. -/
def relPhase : Fin 16 → ℂ := ![1, 1, 1, 1, 1, 1, -I, -I, -I, -I, -I, -I, -I, -I, -I, -I]

theorem relOp_eq_obs (k : Fin 16) : relOp k = relPhase k • obs k := by
  fin_cases k <;> simp [relOp, relPhase, obs, smul_smul]

theorem trace_relOp (k l : Fin 16) :
    ((relOp k)ᴴ * relOp l).trace = if k = l then 4 else 0 := by
  rw [relOp_eq_obs, relOp_eq_obs, Matrix.conjTranspose_smul, obs_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, trace_obs_mul]
  split_ifs with h
  · subst h
    fin_cases k <;> simp [relPhase] <;> ring_nf <;> simp [Complex.I_sq]
  · simp

/-- **The sixteen two-spinor states are orthonormal.** -/
theorem rel_inner (k l : Fin 16) : star (rel k) ⬝ᵥ rel l = if k = l then 1 else 0 := by
  rw [rel_eq_relOf, rel_eq_relOf, dot_relOf, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [MΩ_mul_conjTranspose, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_smul, trace_relOp]
  split_ifs <;> norm_num

theorem rel_linearIndependent : LinearIndependent ℂ rel := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (fun v => star (rel l) ⬝ᵥ v) hg
  simp only [dotProduct_sum, dotProduct_smul, rel_inner, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct_zero] at h
  exact h

/-- The sixteen two-spinor states span all two-spinor states of two systems. -/
theorem rel_span : Submodule.span ℂ (Set.range rel) = ⊤ :=
  rel_linearIndependent.span_eq_top_of_card_eq_finrank (by simp)

/-! ## The values of the comparison and their multiplicities -/

/-- The value of the comparison on the two-spinor state `k`, as an integer: `6 − 2|S|`. -/
def Lvalue (k : Fin 16) : ℤ := 6 - 2 * (disagreeSet k).card

theorem L_rel' (k : Fin 16) : L *ᵥ rel k = ((Lvalue k : ℤ) : ℂ) • rel k := by
  rw [L_rel, Lvalue]
  push_cast
  rfl

/-- The eigenspace of `L` for `μ` is spanned by the two-spinor states with value `μ`. -/
theorem eigenspace_L (μ : ℤ) :
    Module.End.eigenspace (Matrix.toLin' L) (μ : ℂ) =
      Submodule.span ℂ (Set.range fun k : {k : Fin 16 // Lvalue k = μ} => rel k.1) := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
    have hv' : v ∈ Submodule.span ℂ (Set.range rel) := rel_span ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hv'
    obtain ⟨c, rfl⟩ := hv'
    have hc : ∀ k, c k * ((Lvalue k : ℂ) - μ) = 0 := by
      have h0 : ∑ k, (c k * ((Lvalue k : ℂ) - μ)) • rel k = 0 := by
        simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, L_rel', smul_smul] at hv
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, hv, Finset.smul_sum, smul_smul]
        simp only [mul_comm, sub_self]
      exact (Fintype.linearIndependent_iff.mp rel_linearIndependent) _ h0
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : Lvalue k = μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩)
    · have hne : (Lvalue k : ℂ) - μ ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hk
      rw [(mul_eq_zero.mp (hc k)).resolve_right hne, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, L_rel', hk]

theorem finrank_eigenspace_L (μ : ℤ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) (μ : ℂ)) =
      Fintype.card {k : Fin 16 // Lvalue k = μ} := by
  rw [eigenspace_L, finrank_span_eq_card]
  exact rel_linearIndependent.comp _ Subtype.val_injective

/-- **The comparison takes the value 6 once** (the singlet). -/
theorem finrank_eigenspace_L_six :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) = 1 := by
  have := finrank_eigenspace_L 6
  have hc : ((6 : ℤ) : ℂ) = 6 := by norm_num
  rw [hc] at this
  rw [this]
  decide

/-- **The comparison takes the value 2 ten times** (the symmetric states). -/
theorem finrank_eigenspace_L_two :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 10 := by
  have := finrank_eigenspace_L 2
  have hc : ((2 : ℤ) : ℂ) = 2 := by norm_num
  rw [hc] at this
  rw [this]
  decide

/-- **The comparison takes the value −2 five times** (the lines). -/
theorem finrank_eigenspace_L_neg_two :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) (-2)) = 5 := by
  have := finrank_eigenspace_L (-2)
  have hc : ((-2 : ℤ) : ℂ) = -2 := by norm_num
  rw [hc] at this
  rw [this]
  decide

/-- **The comparison takes no other value.** -/
theorem eigenspace_L_other (μ : ℂ) (h6 : μ ≠ 6) (h2 : μ ≠ 2) (hm2 : μ ≠ -2) :
    Module.End.eigenspace (Matrix.toLin' L) μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
  have hv' : v ∈ Submodule.span ℂ (Set.range rel) := rel_span ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hv'
  obtain ⟨c, rfl⟩ := hv'
  have hval : ∀ k, (Lvalue k : ℂ) - μ ≠ 0 := by
    intro k
    have hk : Lvalue k = 6 ∨ Lvalue k = 2 ∨ Lvalue k = -2 := by
      fin_cases k <;> decide
    rcases hk with hk | hk | hk <;> rw [hk, sub_ne_zero] <;> push_cast
    · exact Ne.symm h6
    · exact Ne.symm h2
    · exact Ne.symm hm2
  have hc : ∀ k, c k * ((Lvalue k : ℂ) - μ) = 0 := by
    have h0 : ∑ k, (c k * ((Lvalue k : ℂ) - μ)) • rel k = 0 := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, L_rel', smul_smul] at hv
      simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, hv, Finset.smul_sum, smul_smul]
      simp only [mul_comm, sub_self]
    exact (Fintype.linearIndependent_iff.mp rel_linearIndependent) _ h0
  have : ∀ k, c k = 0 := fun k => (mul_eq_zero.mp (hc k)).resolve_right (hval k)
  simp [this]

/-! ## Disagreement -/

/-- The disagreement operator `6 − L`. -/
def disagreement : Matrix Two Two ℂ := (6 : ℂ) • 1 - L

/-- **The singlet is the only two-spinor state with no disagreement:** `(6 − L) v = 0 ⟺ v ∈ ℂ Ω`. -/
theorem disagreement_eq_zero_iff (v : Two → ℂ) :
    disagreement *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • Ω := by
  have hmem : disagreement *ᵥ v = 0 ↔
      v ∈ Module.End.eigenspace (Matrix.toLin' L) ((6 : ℤ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, disagreement, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
    push_cast
    exact eq_comm
  rw [hmem, eigenspace_L]
  have hS : (Set.range fun k : {k : Fin 16 // Lvalue k = 6} => rel k.1) = {Ω} := by
    ext w
    simp only [Set.mem_range, Set.mem_singleton_iff, Subtype.exists]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : k = 0 := by
        revert hk
        fin_cases k <;> decide
      rw [this, rel_zero]
    · rintro rfl
      exact ⟨0, by decide, rel_zero⟩
  rw [hS, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- **The disagreement is half the sum of the squared differences along the five directions:**
`6 − L = ½ Σ_s (γ_s ⊗ 1 − 1 ⊗ γ_s)²`. -/
theorem disagreement_sum_sq :
    disagreement = (1 / 2 : ℂ) • ∑ s, (γ s ⊗ₖ 1 - 1 ⊗ₖ γ s) * (γ s ⊗ₖ 1 - 1 ⊗ₖ γ s) := by
  have hsq : ∀ s, (γ s ⊗ₖ (1 : Matrix Four Four ℂ) - 1 ⊗ₖ γ s) * (γ s ⊗ₖ 1 - 1 ⊗ₖ γ s) =
      (2 : ℂ) • (1 : Matrix Two Two ℂ) - (2 : ℂ) • (γ s ⊗ₖ γ s) := by
    intro s
    simp only [Matrix.sub_mul, Matrix.mul_sub, ← mul_kronecker_mul, γ_mul_self,
      Matrix.mul_one, Matrix.one_mul, one_kronecker_one]
    module
  simp only [hsq, disagreement, L, one_kronecker_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]
  module

/-! ## Product states disagree by at least four -/

/-- The product two-spinor state `a ⊗ b`. -/
def prodRel (a b : Four → ℂ) : Two → ℂ := fun p => a p.1 * b p.2

theorem kron_mulVec_prodRel (A B : Matrix Four Four ℂ) (a b : Four → ℂ) :
    (A ⊗ₖ B) *ᵥ prodRel a b = prodRel (A *ᵥ a) (B *ᵥ b) := by
  ext ⟨x, y⟩
  simp only [prodRel, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, sum_two]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

theorem dot_prodRel (a b c d : Four → ℂ) :
    star (prodRel a b) ⬝ᵥ prodRel c d = (star a ⬝ᵥ c) * (star b ⬝ᵥ d) := by
  simp only [prodRel, dotProduct, Pi.star_apply, sum_two, star_mul']
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The line of a state (Prop. 8): `n(a)_s = ⟨a, γ_s a⟩`. -/
noncomputable def lineOf (a : Four → ℂ) (s : Fin 5) : ℝ := (star a ⬝ᵥ (γ s *ᵥ a)).re

/-- `⟨a, γ_s a⟩` is real. -/
theorem lineOf_im (a : Four → ℂ) (s : Fin 5) : (star a ⬝ᵥ (γ s *ᵥ a)).im = 0 := by
  fin_cases s <;>
    simp [γ, σ₁, σ₂, σ₃, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring

theorem dot_γ_eq (a : Four → ℂ) (s : Fin 5) :
    star a ⬝ᵥ (γ s *ᵥ a) = (lineOf a s : ℂ) := by
  apply Complex.ext
  · simp [lineOf]
  · simp [lineOf_im]

/-- The length of a state, a real number. -/
noncomputable def normSq (a : Four → ℂ) : ℝ := (star a ⬝ᵥ a).re

theorem dot_self_eq (a : Four → ℂ) : star a ⬝ᵥ a = (normSq a : ℂ) := by
  apply Complex.ext
  · simp [normSq]
  · simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring

/-- **Every state lies on one line:** `Σ_s ⟨a, γ_s a⟩² = ⟨a, a⟩²`. -/
theorem sum_lineOf_sq (a : Four → ℂ) : ∑ s, lineOf a s ^ 2 = normSq a ^ 2 := by
  simp [lineOf, normSq, Fin.sum_univ_five, γ, σ₁, σ₂, σ₃, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- **The line of a unit state is a unit vector:** every state lies on the plus side of one line. -/
theorem lineOf_unit (a : Four → ℂ) (ha : normSq a = 1) : ∑ s, lineOf a s ^ 2 = 1 := by
  rw [sum_lineOf_sq, ha, one_pow]

theorem normSq_nonneg (a : Four → ℂ) : 0 ≤ normSq a := by
  simp only [normSq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (a i).re, sq_nonneg (a i).im]

/-- The disagreement of the product `a ⊗ b` is `5 |a|² |b|² − m(a)·m(b)`. -/
theorem disagreement_prodRel (a b : Four → ℂ) :
    star (prodRel a b) ⬝ᵥ (disagreement *ᵥ prodRel a b) =
      ((5 * normSq a * normSq b - ∑ s, lineOf a s * lineOf b s : ℝ) : ℂ) := by
  rw [disagreement, L, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_add,
    dotProduct_sum]
  simp only [kron_mulVec_prodRel, dot_prodRel, Matrix.one_mulVec, dot_self_eq, dot_γ_eq]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- **Two systems prepared apart disagree by at least four:** for unit states `a` and `b`, the
disagreement of `a ⊗ b` is at least `4`. -/
theorem disagreement_prodRel_ge (a b : Four → ℂ) (ha : normSq a = 1) (hb : normSq b = 1) :
    4 ≤ (star (prodRel a b) ⬝ᵥ (disagreement *ᵥ prodRel a b)).re := by
  rw [disagreement_prodRel, Complex.ofReal_re, ha, hb]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (lineOf a) (lineOf b)
  rw [sum_lineOf_sq, sum_lineOf_sq, ha, hb] at hcs
  nlinarith [hcs]

end Comparison

end
