module

public import Comparison.Elements.OneModel

/-!
# Proposition 1 (iii): the normal form of every quaternionic structure

`H` is a finite-dimensional complex inner-product space (P1) and `Θ` an antiunitary map with
`Θ² = −1` (P3 (a)), bundled as `Partner H`.

* `Partner.inner_self_Θ`, `Partner.norm_Θ`: every state is perpendicular to its conjugate and as
  long (Prop. 1 (i)).
* `Partner.exists_normal_basis`: `H` has an orthonormal basis `u₁, −Θu₁, …, u_n, −Θu_n`, indexed by
  `Fin n × Fin 2`; so `dim H = 2n` (`Partner.finrank_eq`).
* `Partner.coord_Θ`: in that basis the coordinates of `Θ v` are `J_n` times the conjugate
  coordinates of `v`: `Θ = J_n K` with `J_n = 1 ⊗ ε` the standard join of `OneModel.lean`.

So every quaternionic structure is the standard one, up to a unitary change of basis.
-/

@[expose] public section

namespace Comparison

open scoped InnerProductSpace
open Matrix hiding J
open Complex Kronecker

/-- A quaternionic structure on `H` (P3 (a)): additive, antilinear, antiunitary, and `Θ² = −1`. -/
structure Partner (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The quaternionic structure map. -/
  Θ : H → H
  map_add : ∀ v w, Θ (v + w) = Θ v + Θ w
  map_smul : ∀ (c : ℂ) v, Θ (c • v) = star c • Θ v
  inner_Θ : ∀ v w, ⟪Θ v, Θ w⟫_ℂ = ⟪w, v⟫_ℂ
  Θ_Θ : ∀ v, Θ (Θ v) = -v

namespace Partner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (T : Partner H)

theorem inner_Θ_self (v : H) : ⟪T.Θ v, v⟫_ℂ = 0 := by
  have h := T.inner_Θ v (T.Θ v)
  rw [T.Θ_Θ, inner_neg_right] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- **Every state is perpendicular to its conjugate.** -/
theorem inner_self_Θ (v : H) : ⟪v, T.Θ v⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_Θ_self, map_zero]

/-- **The conjugate is as long as the state.** -/
theorem norm_Θ (v : H) : ‖T.Θ v‖ = ‖v‖ := by
  have h := T.inner_Θ v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖T.Θ v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

/-- If `w ⊥ Θ x` then `Θ w ⊥ x`. -/
theorem inner_Θ_right_of (x w : H) (h : ⟪T.Θ x, w⟫_ℂ = 0) : ⟪x, T.Θ w⟫_ℂ = 0 := by
  have h1 := T.inner_Θ (T.Θ x) w
  have h2 : ⟪w, T.Θ x⟫_ℂ = 0 := by rw [← inner_conj_symm, h, map_zero]
  rw [T.Θ_Θ, inner_neg_left, h2] at h1
  exact neg_eq_zero.mp h1

/-- If `w ⊥ x` then `Θ w ⊥ Θ x`. -/
theorem inner_Θ_Θ_of (x w : H) (h : ⟪x, w⟫_ℂ = 0) : ⟪T.Θ x, T.Θ w⟫_ℂ = 0 := by
  rw [T.inner_Θ, ← inner_conj_symm, h, map_zero]

/-- `dim H = 2n`: a system with a quaternionic structure has an even number of complex dimensions. -/
theorem finrank_eq {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H) :
    Module.finrank ℂ H = 2 * n := by
  rw [Module.finrank_eq_card_basis b.toBasis]
  simp [mul_comm]

variable [FiniteDimensional ℂ H]

/-- **The pairs of a quaternionic structure.** Every subspace `K` kept by `Θ` has unit vectors `u₁, …, u_n` in
`K` such that `u_k` is perpendicular to `u_l` and to `Θ u_l` for `k ≠ l`, with `2n = dim K`. -/
theorem exists_pairs (d : ℕ) : ∀ K : Submodule ℂ H, Module.finrank ℂ K = d →
    (∀ x ∈ K, T.Θ x ∈ K) →
    ∃ n : ℕ, ∃ u : Fin n → H, (∀ k, u k ∈ K) ∧ (∀ k, ‖u k‖ = 1) ∧
      (∀ k l, k ≠ l → ⟪u k, u l⟫_ℂ = 0 ∧ ⟪u k, T.Θ (u l)⟫_ℂ = 0) ∧ 2 * n = d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K hd hK
  by_cases hK0 : K = ⊥
  · refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
    rw [← hd, hK0, finrank_bot]
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  set y : H := ((‖x‖ : ℂ)⁻¹) • x with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  have hyK : y ∈ K := K.smul_mem _ hxK
  have hΘyK : T.Θ y ∈ K := hK y hyK
  set S : Submodule ℂ H := Submodule.span ℂ (Set.range ![y, T.Θ y]) with hS
  have hyS : y ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hΘyS : T.Θ y ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have hSK : S ≤ K := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hyK
    · exact hΘyK
  have horth : Orthonormal ℂ ![y, T.Θ y] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simp [hy1]
    · simp [inner_self_Θ]
    · simp [inner_Θ_self]
    · simp [T.norm_Θ, hy1]
  have hS2 : Module.finrank ℂ S = 2 := by
    rw [hS, finrank_span_eq_card horth.linearIndependent]
    simp
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal hSK
  rw [hS2, hd] at hdim
  have memS : ∀ w, w ∈ Sᗮ ↔ ⟪y, w⟫_ℂ = 0 ∧ ⟪T.Θ y, w⟫_ℂ = 0 := by
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
  set K' : Submodule ℂ H := Sᗮ ⊓ K with hK'
  have hK'Θ : ∀ w ∈ K', T.Θ w ∈ K' := by
    intro w hw
    rw [hK', Submodule.mem_inf] at hw ⊢
    obtain ⟨hwS, hwK⟩ := hw
    rw [memS] at hwS ⊢
    exact ⟨⟨T.inner_Θ_right_of y w hwS.2, T.inner_Θ_Θ_of y w hwS.1⟩, hK w hwK⟩
  obtain ⟨n', u', hu'K, hu'1, hu'2, hn'⟩ :=
    ih (d - 2) (by omega) K' (by omega) hK'Θ
  have hu'S : ∀ k, ⟪y, u' k⟫_ℂ = 0 ∧ ⟪T.Θ y, u' k⟫_ℂ = 0 := fun k =>
    (memS (u' k)).mp (Submodule.mem_inf.mp (hu'K k)).1
  have hΘu'S : ∀ k, ⟪y, T.Θ (u' k)⟫_ℂ = 0 := fun k =>
    ((memS _).mp (Submodule.mem_inf.mp (hK'Θ _ (hu'K k))).1).1
  refine ⟨n' + 1, Fin.cons y u', ?_, ?_, ?_, by omega⟩
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
          rw [← inner_conj_symm, (hu'S k).1, map_zero]
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← inner_conj_symm, (hu'S k).2, map_zero]
      | succ l =>
        simp only [Fin.cons_succ]
        exact hu'2 k l (fun h => hkl (by rw [h]))

/-- The family `u₁, −Θu₁, …, u_n, −Θu_n` of the pairs. -/
def pairs {n : ℕ} (u : Fin n → H) : Fin n × Fin 2 → H := fun p => ![u p.1, -T.Θ (u p.1)] p.2

omit [FiniteDimensional ℂ H] in
theorem pairs_orthonormal {n : ℕ} (u : Fin n → H) (h1 : ∀ k, ‖u k‖ = 1)
    (h2 : ∀ k l, k ≠ l → ⟪u k, u l⟫_ℂ = 0 ∧ ⟪u k, T.Θ (u l)⟫_ℂ = 0) :
    Orthonormal ℂ (T.pairs u) := by
  rw [orthonormal_iff_ite]
  rintro ⟨k, a⟩ ⟨l, b⟩
  by_cases hkl : k = l
  · subst hkl
    fin_cases a <;> fin_cases b
    · simp [pairs, h1 k]
    · simp [pairs, inner_self_Θ]
    · simp [pairs, inner_Θ_self]
    · simp [pairs, T.norm_Θ, h1 k]
  · have hne : (k, a) ≠ (l, b) := fun h => hkl (congrArg Prod.fst h)
    obtain ⟨hA, hB⟩ := h2 k l hkl
    obtain ⟨hC, hD⟩ := h2 l k (Ne.symm hkl)
    have hB' : ⟪T.Θ (u k), u l⟫_ℂ = 0 := by rw [← inner_conj_symm, hD, map_zero]
    have hE : ⟪T.Θ (u k), T.Θ (u l)⟫_ℂ = 0 :=
      T.inner_Θ_Θ_of _ _ (by rw [← inner_conj_symm, hC, map_zero])
    fin_cases a <;> fin_cases b <;> simp [pairs, hkl, hA, hB, hB', hE]

/-- **The normal form of the quaternionic structure** (Prop. 1 (iii)): `H` has an orthonormal basis
`u₁, −Θu₁, …, u_n, −Θu_n`. -/
theorem exists_normal_basis :
    ∃ n : ℕ, ∃ b : OrthonormalBasis (Fin n × Fin 2) ℂ H, ∀ k, b (k, 1) = -T.Θ (b (k, 0)) := by
  obtain ⟨n, u, -, h1, h2, hn⟩ :=
    T.exists_pairs (Module.finrank ℂ (⊤ : Submodule ℂ H)) ⊤ rfl (fun x _ => Submodule.mem_top)
  have hon := T.pairs_orthonormal u h1 h2
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range (T.pairs u)) := by
    have h := finrank_span_eq_card hon.linearIndependent
    rw [finrank_top] at hn
    have htop : Submodule.span ℂ (Set.range (T.pairs u)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h]; simp; omega)
    rw [htop]
  refine ⟨n, OrthonormalBasis.mk hon hsp, fun k => ?_⟩
  simp [pairs]

theorem Jn_mulVec (n : ℕ) (w : Fin n × Fin 2 → ℂ) (k : Fin n) (a : Fin 2) :
    (Jn n *ᵥ w) (k, a) = ε a 0 * w (k, 0) + ε a 1 * w (k, 1) := by
  simp [Jn, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Fin.sum_univ_two]

omit [FiniteDimensional ℂ H] in
/-- **In the normal basis the quaternionic structure is `J_n K`:** the coordinates `⟪b p, Θ v⟫` of `Θ v` are
`J_n` times the conjugate coordinates of `v`. -/
theorem coord_Θ {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) (v : H) (p : Fin n × Fin 2) :
    ⟪b p, T.Θ v⟫_ℂ = (Jn n *ᵥ fun q => star ⟪b q, v⟫_ℂ) p := by
  have hb0 : ∀ k, b (k, 0) = T.Θ (b (k, 1)) := by
    intro k
    rw [hb k]
    have h := T.map_smul (-1) (T.Θ (b (k, 0)))
    rw [neg_one_smul] at h
    rw [h, T.Θ_Θ]
    simp
  obtain ⟨k, a⟩ := p
  rw [Jn_mulVec]
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [hb0 k, T.inner_Θ, ← inner_conj_symm]
    simp [ε]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [hb k, inner_neg_left, T.inner_Θ, ← inner_conj_symm]
    simp [ε]

end Partner

end Comparison

end
