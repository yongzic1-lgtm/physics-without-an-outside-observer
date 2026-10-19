import Comparison.Elements.OneModel
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module

/-!
# The dimension of the distinctions for every `n` (Proposition 2; Proposition A2 of the public edition)

On `H = ℂ^{2n}` (`Fin n × Fin 2`) with the quaternionic structure `Θv = J_n v̄`, `J_n = 1 ⊗ ε`, the distinctions are the Hermitian
operators of trace zero that commute with `Θ` (`Elements/OneModel.lean`: `IsDistinctionN`). In blocks they are the
quaternionic Hermitian matrices `[[α_{ij}, β_{ij}], [−β̄_{ij}, ᾱ_{ij}]]` with `α` Hermitian and `β` antisymmetric:

* `W_rel`, `W_herm`: the block form of an operator that is Hermitian and commutes with `Θ`;
* `Wequiv`: those operators form a real space isomorphic to `ℝⁿ × ℂ^{n(n−1)/2} × ℂ^{n(n−1)/2}` (the diagonal of `α`,
  the upper `α` and the upper `β`), so `finrank_W`: their real dimension is `2n² − n`;
* `finrank_distinctions` (**Proposition 2**): **`dim Q = 2n² − n − 1`** for every `n ≥ 1`, trace zero taking one
  away.
-/

namespace Comparison.Article

open Matrix Module

/-- The strictly upper pairs of `Fin n`. -/
abbrev Up (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The operators on `ℂ^{2n}` that are Hermitian and commute with the quaternionic structure. -/
def Wsub (n : ℕ) : Submodule ℝ (Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) where
  carrier := {a | aᴴ = a ∧ a * Jn n = Jn n * a.map star}
  add_mem' {a b} ha hb := by
    refine ⟨by rw [Matrix.conjTranspose_add, ha.1, hb.1], ?_⟩
    rw [Matrix.add_mul, ha.2, hb.2, ← Matrix.mul_add]
    congr 1
    ext i j
    simp
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    refine ⟨?_, ?_⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply] at this ⊢
      rw [← this]
      simp [Complex.ext_iff]
    · have hm : (c • a).map star = c • a.map star := by
        ext i j
        simp [Complex.ext_iff]
      rw [Matrix.smul_mul, ha.2, hm, Matrix.mul_smul]

theorem Jn_apply (n : ℕ) (k j : Fin n) (u t : Fin 2) :
    Jn n (k, u) (j, t) = if k = j then ε u t else 0 := by
  simp [Jn, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem mul_Jn_apply {n : ℕ} (a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) (p : Fin n × Fin 2) (j : Fin n)
    (t : Fin 2) : (a * Jn n) p (j, t) = a p (j, 0) * ε 0 t + a p (j, 1) * ε 1 t := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Jn_apply, Fin.sum_univ_two]

theorem Jn_mul_apply {n : ℕ} (b : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) (i : Fin n) (s : Fin 2)
    (q : Fin n × Fin 2) : (Jn n * b) (i, s) q = ε s 0 * b (i, 0) q + ε s 1 * b (i, 1) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Jn_apply, Fin.sum_univ_two]

/-- **The block form:** the lower blocks are `ᾱ` and `−β̄`. -/
theorem W_rel {n : ℕ} {a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ} (hJ : a * Jn n = Jn n * a.map star)
    (i j : Fin n) : a (i, 1) (j, 1) = star (a (i, 0) (j, 0)) ∧ a (i, 1) (j, 0) = -star (a (i, 0) (j, 1)) := by
  have h01 := congrFun (congrFun hJ (i, 0)) (j, 1)
  have h00 := congrFun (congrFun hJ (i, 0)) (j, 0)
  rw [mul_Jn_apply, Jn_mul_apply] at h01 h00
  simp [ε, Matrix.map_apply] at h01 h00
  constructor
  · rw [h01]
    simp [Complex.star_def]
  · have := congrArg star h00
    simp at this
    rw [← this]
    simp

/-- **`α` is Hermitian and `β` antisymmetric.** -/
theorem W_herm {n : ℕ} {a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ} (ha : aᴴ = a)
    (hJ : a * Jn n = Jn n * a.map star) (i j : Fin n) :
    a (j, 0) (i, 0) = star (a (i, 0) (j, 0)) ∧ a (j, 0) (i, 1) = -a (i, 0) (j, 1) := by
  have h1 := congrFun (congrFun ha (j, 0)) (i, 0)
  have h2 := congrFun (congrFun ha (j, 0)) (i, 1)
  simp only [Matrix.conjTranspose_apply] at h1 h2
  refine ⟨h1.symm, ?_⟩
  rw [← h2, (W_rel hJ i j).2]
  simp

/-- The quaternion block `[[α, β], [−β̄, ᾱ]]`. -/
def qblock (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![α, β; -star β, star α]

/-- The diagonal and upper `α`, and the upper `β`, back to an operator. -/
noncomputable def alphaOf {n : ℕ} (d : Fin n → ℝ) (x : Up n → ℂ) (i j : Fin n) : ℂ :=
  if h : i < j then x ⟨(i, j), h⟩ else if h' : j < i then star (x ⟨(j, i), h'⟩) else (d i : ℂ)

noncomputable def betaOf {n : ℕ} (y : Up n → ℂ) (i j : Fin n) : ℂ :=
  if h : i < j then y ⟨(i, j), h⟩ else if h' : j < i then -y ⟨(j, i), h'⟩ else 0

noncomputable def matOf {n : ℕ} (d : Fin n → ℝ) (x y : Up n → ℂ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  Matrix.of fun p q => qblock (alphaOf d x p.1 q.1) (betaOf y p.1 q.1) p.2 q.2

theorem alphaOf_swap {n : ℕ} (d : Fin n → ℝ) (x : Up n → ℂ) (i j : Fin n) :
    alphaOf d x j i = star (alphaOf d x i j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [alphaOf, h, not_lt_of_gt h]
  · simp [alphaOf]
  · simp [alphaOf, h, not_lt_of_gt h]

theorem betaOf_swap {n : ℕ} (y : Up n → ℂ) (i j : Fin n) : betaOf y j i = -betaOf y i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [betaOf, h, not_lt_of_gt h]
  · simp [betaOf]
  · simp [betaOf, h, not_lt_of_gt h]

theorem matOf_mem {n : ℕ} (d : Fin n → ℝ) (x y : Up n → ℂ) : matOf d x y ∈ Wsub n := by
  refine ⟨?_, ?_⟩
  · ext ⟨i, s⟩ ⟨j, t⟩
    simp only [Matrix.conjTranspose_apply, matOf, Matrix.of_apply]
    rw [alphaOf_swap d x i j, betaOf_swap y i j]
    fin_cases s <;> fin_cases t <;> simp [qblock]
  · ext ⟨i, s⟩ ⟨j, t⟩
    rw [mul_Jn_apply, Jn_mul_apply]
    simp only [matOf, Matrix.of_apply, Matrix.map_apply]
    fin_cases s <;> fin_cases t <;> simp [qblock, ε]

/-- From an operator to its coordinates. -/
noncomputable def Phi (n : ℕ) : Wsub n →ₗ[ℝ] (Fin n → ℝ) × (Up n → ℂ) × (Up n → ℂ) where
  toFun a := (fun i => (a.1 (i, 0) (i, 0)).re, fun p => a.1 (p.1.1, 0) (p.1.2, 0),
    fun p => a.1 (p.1.1, 0) (p.1.2, 1))
  map_add' a b := by
    ext <;> simp
  map_smul' c a := by
    ext <;> simp

theorem diag_real {n : ℕ} {a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ} (ha : aᴴ = a) (i : Fin n) :
    ((a (i, 0) (i, 0)).re : ℂ) = a (i, 0) (i, 0) := by
  have h := congrFun (congrFun ha (i, 0)) (i, 0)
  simp only [Matrix.conjTranspose_apply] at h
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp at this
    simp
    linarith

theorem diag_beta_zero {n : ℕ} {a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ} (ha : aᴴ = a)
    (hJ : a * Jn n = Jn n * a.map star) (i : Fin n) : a (i, 0) (i, 1) = 0 := by
  have h := (W_herm ha hJ i i).2
  have : (2 : ℂ) * a (i, 0) (i, 1) = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  simpa using this

/-- **The operators that are Hermitian and commute with the quaternionic structure, as a real space.** -/
noncomputable def Wequiv (n : ℕ) : Wsub n ≃ₗ[ℝ] (Fin n → ℝ) × (Up n → ℂ) × (Up n → ℂ) :=
  { Phi n with
    invFun := fun v => ⟨matOf v.1 v.2.1 v.2.2, matOf_mem _ _ _⟩
    left_inv := by
      rintro ⟨a, ha, hJ⟩
      apply Subtype.ext
      ext ⟨i, s⟩ ⟨j, t⟩
      simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, matOf, Matrix.of_apply]
      have hα : alphaOf (fun i => (a (i, 0) (i, 0)).re) (fun p => a (p.1.1, 0) (p.1.2, 0)) i j = a (i, 0) (j, 0) := by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [alphaOf, h]
        · simp [alphaOf, diag_real ha]
        · simp [alphaOf, h, not_lt_of_gt h, (W_herm ha hJ j i).1]
      have hβ : betaOf (fun p => a (p.1.1, 0) (p.1.2, 1)) i j = a (i, 0) (j, 1) := by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [betaOf, h]
        · simp [betaOf, diag_beta_zero ha hJ]
        · simp [betaOf, h, not_lt_of_gt h, (W_herm ha hJ j i).2]
      rw [hα, hβ]
      fin_cases s <;> fin_cases t <;> simp [qblock, (W_rel hJ i j).1, (W_rel hJ i j).2]
    right_inv := by
      rintro ⟨d, x, y⟩
      simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, matOf, Matrix.of_apply]
      ext
      · simp [qblock, alphaOf]
      · simp [qblock, alphaOf, (show _ < _ from ‹Up n›.2)]
      · simp [qblock, betaOf, (show _ < _ from ‹Up n›.2)] }

theorem card_up (n : ℕ) : 2 * Fintype.card (Up n) = n * n - n := by
  rw [Fintype.card_subtype]
  have hsw : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp; simpa using hp
    · intro p _ q _ h; simpa using h
    · intro q hq; exact ⟨q.swap, by simpa using hq, by simp⟩
  have hoff : (Finset.univ : Finset (Fin n)).offDiag =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) ∪
        (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdis : Disjoint (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
      (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1 h2
  have hc := Finset.offDiag_card (Finset.univ : Finset (Fin n))
  rw [hoff, Finset.card_union_of_disjoint hdis, ← hsw, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- **The real dimension of the Hermitian operators that commute with the quaternionic structure: `2n² − n`.** -/
theorem finrank_W (n : ℕ) : finrank ℝ (Wsub n) = 2 * n ^ 2 - n := by
  rw [(Wequiv n).finrank_eq, Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h := card_up n
  have hn : n ≤ n * n := Nat.le_mul_self n
  rw [sq]
  omega

/-- The trace's real part, on `W`. -/
noncomputable def traceRe (n : ℕ) : Wsub n →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (Matrix.traceLinearMap (Fin n × Fin 2) ℝ ℂ) ∘ₗ (Wsub n).subtype

theorem trace_matOf {n : ℕ} (d : Fin n → ℝ) (x y : Up n → ℂ) :
    (matOf d x y).trace = 2 * ∑ i, (d i : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, matOf, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [qblock, alphaOf]
  ring

theorem trace_W_real {n : ℕ} (a : Wsub n) : ((a.1.trace).re : ℂ) = a.1.trace := by
  have h := (Wequiv n).left_inv a
  have e : a.1 = matOf ((Phi n) a).1 ((Phi n) a).2.1 ((Phi n) a).2.2 := by
    conv_lhs => rw [← h]
    rfl
  rw [e, trace_matOf]
  simp

theorem traceRe_surjective (n : ℕ) (hn : 0 < n) : Function.Surjective (traceRe n) := by
  intro c
  refine ⟨⟨matOf (Pi.single ⟨0, hn⟩ (c / 2)) 0 0, matOf_mem _ _ _⟩, ?_⟩
  simp only [traceRe, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Matrix.traceLinearMap_apply, Complex.reLm_coe, trace_matOf]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb]) (by simp)]
  simp
  ring

/-- **The distinctions on `ℂ^{2n}`**, as a real space. -/
noncomputable def distinctions (n : ℕ) : Submodule ℝ (Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :=
  (LinearMap.ker (traceRe n)).map (Wsub n).subtype

theorem mem_distinctions {n : ℕ} (a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    a ∈ distinctions n ↔ IsDistinctionN n a := by
  constructor
  · rintro ⟨⟨b, hb⟩, hk, rfl⟩
    have hr : (b.trace).re = 0 := hk
    have ht := trace_W_real ⟨b, hb⟩
    simp only at ht
    refine ⟨hb.1, ?_, hb.2⟩
    change b.trace = 0
    rw [← ht, hr, Complex.ofReal_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨a, h1, h3⟩, ?_, rfl⟩
    change (a.trace).re = 0
    rw [h2, Complex.zero_re]

/-- **Proposition 2: `dim Q = 2n² − n − 1`** for every `n ≥ 1`. -/
theorem finrank_distinctions (n : ℕ) (hn : 0 < n) : finrank ℝ (distinctions n) = 2 * n ^ 2 - n - 1 := by
  have hinj : Function.Injective (Wsub n).subtype := Subtype.val_injective
  rw [distinctions, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  have hrk := LinearMap.finrank_range_add_finrank_ker (traceRe n)
  rw [LinearMap.range_eq_top.mpr (traceRe_surjective n hn), finrank_top, Module.finrank_self, finrank_W] at hrk
  omega

end Comparison.Article
