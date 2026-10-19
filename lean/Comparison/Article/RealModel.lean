import Comparison.Elements.Observables
import Comparison.Elements.OneModel

/-!
# The square root of the sign uses P1's `i` (Proposition 20; Proposition A20 of the public edition)

* **The real model of P1** on `ℝ² ⊗ ℝ²`: the quaternionic structure `Θ = 1 ⊗ ε` is orthogonal, `Θᵀ = −Θ`, `Θ² = −1`
  (`realJ_props`); its distinctions, symmetric of trace zero and commuting with `Θ`, are exactly the span of
  `σ₃ ⊗ 1`, `σ₁ ⊗ 1`, `ε ⊗ ε`, a space of dimension three, the Hermitian `2 × 2` matrices of trace zero
  (`realQ_eq_span`, `finrank_realQ`), and each squares to a number (`realQ_sq`).
* **The complex model:** `Θ(i v) = −i Θ(v)`, so `i`, `Θ` and `iΘ` anticommute (`I_Θ_anticomm`), and there are
  five lines (`Elements/OneModel.lean`).
* **A real half fails:** a real `q` with `q² = θ_D` on `k` reversed directions has `(det q)² = (−1)^k`, so
  `k` is even (`real_half_det`).
* **The spans:** on `ℝ² ⊗ ℝ²` the products of symmetric operators span nine of the ten symmetric operators,
  `ε ⊗ ε` being symmetric and orthogonal to all of them (`realProducts_nine`); on `ℂ² ⊗ ℂ²` the products of
  Hermitian operators span all sixteen (`complexProducts_all`).
-/

namespace Comparison.Article

open Matrix hiding J
open Kronecker

/-! ## The real model -/

/-- The real `ε`. -/
def epsR : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
def s1R : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def s3R : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- **The real structure** `Θ = 1 ⊗ ε` on `ℝ² ⊗ ℝ²`. -/
def realJ : Matrix Four Four ℝ := (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ epsR

theorem realJ_props : realJᵀ = -realJ ∧ realJ * realJ = -1 ∧ realJᵀ * realJ = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> simp [realJ, epsR, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply])

/-- **The distinctions of the real model:** symmetric, of trace zero, commuting with `Θ`. -/
def realQ : Submodule ℝ (Matrix Four Four ℝ) where
  carrier := {X | Xᵀ = X ∧ X.trace = 0 ∧ X * realJ = realJ * X}
  add_mem' := by
    rintro X Y ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨by rw [Matrix.transpose_add, h1, k1], by rw [Matrix.trace_add, h2, k2, add_zero], ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, h3, k3]
  zero_mem' := by simp
  smul_mem' := by
    rintro c X ⟨h1, h2, h3⟩
    refine ⟨by rw [Matrix.transpose_smul, h1], by rw [Matrix.trace_smul, h2, smul_zero], ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, h3]

/-- The three real lines `σ₃ ⊗ 1`, `σ₁ ⊗ 1`, `ε ⊗ ε`. -/
def realLines : Fin 3 → Matrix Four Four ℝ :=
  ![s3R ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ), s1R ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ), epsR ⊗ₖ epsR]

theorem realLines_mem (i : Fin 3) : realLines i ∈ realQ := by
  refine ⟨?_, ?_, ?_⟩ <;> fin_cases i <;>
    first
    | (ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [realLines, realJ, epsR, s1R, s3R, Matrix.mul_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, Matrix.one_apply])
    | simp [realLines, epsR, s1R, s3R, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.one_apply]

theorem realLines_linearIndependent : LinearIndependent ℝ realLines := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have e := fun a b => congrFun (congrFun hc a) b
  have h00 := e (0, 0) (0, 0)
  have h01 := e (0, 0) (1, 0)
  have h03 := e (0, 0) (1, 1)
  simp [realLines, epsR, s1R, s3R, Fin.sum_univ_three, Matrix.one_apply] at h00 h01 h03
  fin_cases i <;> simp <;> linarith

theorem realQ_entries (X : Matrix Four Four ℝ) (hX : X ∈ realQ) :
    X = X (0, 0) (0, 0) • realLines 0 + X (0, 0) (1, 0) • realLines 1 + X (0, 0) (1, 1) • realLines 2 := by
  obtain ⟨h1, h2, h3⟩ := hX
  have s1 : X (0, 0) (0, 0) = X (0, 0) (0, 0) := by have := congrFun (congrFun h1 (0, 0)) (0, 0); simpa using this
  have s2 : X (0, 0) (0, 1) = X (0, 1) (0, 0) := by have := congrFun (congrFun h1 (0, 1)) (0, 0); simpa using this
  have s3 : X (0, 0) (1, 0) = X (1, 0) (0, 0) := by have := congrFun (congrFun h1 (1, 0)) (0, 0); simpa using this
  have s4 : X (0, 0) (1, 1) = X (1, 1) (0, 0) := by have := congrFun (congrFun h1 (1, 1)) (0, 0); simpa using this
  have s5 : X (0, 1) (0, 0) = X (0, 0) (0, 1) := by have := congrFun (congrFun h1 (0, 0)) (0, 1); simpa using this
  have s6 : X (0, 1) (0, 1) = X (0, 1) (0, 1) := by have := congrFun (congrFun h1 (0, 1)) (0, 1); simpa using this
  have s7 : X (0, 1) (1, 0) = X (1, 0) (0, 1) := by have := congrFun (congrFun h1 (1, 0)) (0, 1); simpa using this
  have s8 : X (0, 1) (1, 1) = X (1, 1) (0, 1) := by have := congrFun (congrFun h1 (1, 1)) (0, 1); simpa using this
  have s9 : X (1, 0) (0, 0) = X (0, 0) (1, 0) := by have := congrFun (congrFun h1 (0, 0)) (1, 0); simpa using this
  have s10 : X (1, 0) (0, 1) = X (0, 1) (1, 0) := by have := congrFun (congrFun h1 (0, 1)) (1, 0); simpa using this
  have s11 : X (1, 0) (1, 0) = X (1, 0) (1, 0) := by have := congrFun (congrFun h1 (1, 0)) (1, 0); simpa using this
  have s12 : X (1, 0) (1, 1) = X (1, 1) (1, 0) := by have := congrFun (congrFun h1 (1, 1)) (1, 0); simpa using this
  have s13 : X (1, 1) (0, 0) = X (0, 0) (1, 1) := by have := congrFun (congrFun h1 (0, 0)) (1, 1); simpa using this
  have s14 : X (1, 1) (0, 1) = X (0, 1) (1, 1) := by have := congrFun (congrFun h1 (0, 1)) (1, 1); simpa using this
  have s15 : X (1, 1) (1, 0) = X (1, 0) (1, 1) := by have := congrFun (congrFun h1 (1, 0)) (1, 1); simpa using this
  have s16 : X (1, 1) (1, 1) = X (1, 1) (1, 1) := by have := congrFun (congrFun h1 (1, 1)) (1, 1); simpa using this
  have c1 := congrFun (congrFun h3 (0, 0)) (0, 0)
  have c2 := congrFun (congrFun h3 (0, 0)) (0, 1)
  have c3 := congrFun (congrFun h3 (0, 0)) (1, 0)
  have c4 := congrFun (congrFun h3 (0, 0)) (1, 1)
  have c5 := congrFun (congrFun h3 (0, 1)) (0, 0)
  have c6 := congrFun (congrFun h3 (0, 1)) (0, 1)
  have c7 := congrFun (congrFun h3 (0, 1)) (1, 0)
  have c8 := congrFun (congrFun h3 (0, 1)) (1, 1)
  have c9 := congrFun (congrFun h3 (1, 0)) (0, 0)
  have c10 := congrFun (congrFun h3 (1, 0)) (0, 1)
  have c11 := congrFun (congrFun h3 (1, 0)) (1, 0)
  have c12 := congrFun (congrFun h3 (1, 0)) (1, 1)
  have c13 := congrFun (congrFun h3 (1, 1)) (0, 0)
  have c14 := congrFun (congrFun h3 (1, 1)) (0, 1)
  have c15 := congrFun (congrFun h3 (1, 1)) (1, 0)
  have c16 := congrFun (congrFun h3 (1, 1)) (1, 1)
  have t : X (0, 0) (0, 0) + X (0, 1) (0, 1) + X (1, 0) (1, 0) + X (1, 1) (1, 1) = 0 := by
    simpa [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using h2
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, realJ, Matrix.kroneckerMap_apply,
    epsR, Matrix.one_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [realLines, epsR, s1R, s3R, Matrix.one_apply] <;> norm_num at * <;> linarith

theorem realQ_eq_span : realQ = Submodule.span ℝ (Set.range realLines) := by
  apply le_antisymm
  · intro X hX
    rw [realQ_entries X hX]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact realLines_mem i

/-- **With real P1 there are three lines:** `dim Q = 3`. -/
theorem finrank_realQ : Module.finrank ℝ realQ = 3 := by
  rw [realQ_eq_span, finrank_span_eq_card realLines_linearIndependent]
  simp

/-- The three real lines anticommute and square to one: every distinction squares to a number. -/
theorem realLines_clifford (i j : Fin 3) :
    realLines i * realLines j + realLines j * realLines i = (if i = j then 2 else 0 : ℝ) • 1 := by
  fin_cases i <;> fin_cases j <;>
    (ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [realLines, epsR, s1R, s3R, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.one_apply] <;> norm_num)

/-! ## The complex model: `i`, `Θ` and `iΘ` anticommute -/

theorem I_Θ_anticomm (v : Four → ℂ) : Θ (Complex.I • v) = -(Complex.I • Θ v) := by
  rw [Θ_smul]
  simp [Complex.conj_I]

/-! ## A real half fails -/

/-- **`(det q)² = (−1)^k`**: a real `q` whose square reverses `k` directions has `k` even. -/
theorem real_half_det {n : Type*} [Fintype n] [DecidableEq n] (q : Matrix n n ℝ) (D : Finset n)
    (hq : q * q = Matrix.diagonal fun i => if i ∈ D then -1 else 1) :
    q.det ^ 2 = (-1) ^ D.card ∧ Even D.card := by
  have h : q.det ^ 2 = (-1 : ℝ) ^ D.card := by
    rw [sq, ← Matrix.det_mul, hq, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
    simp [Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine ⟨h, ?_⟩
  rcases Nat.even_or_odd D.card with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_pow] at h
    nlinarith [sq_nonneg q.det]

/-! ## The spans -/

/-- The three symmetric `2 × 2` real matrices. -/
def symR : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![0, 1; 1, 0]]

/-- The nine products of symmetric operators on `ℝ² ⊗ ℝ²`. -/
def realProducts : Fin 3 × Fin 3 → Matrix Four Four ℝ := fun p => symR p.1 ⊗ₖ symR p.2

theorem realProducts_linearIndependent : LinearIndependent ℝ realProducts := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have e := fun a b => congrFun (congrFun hc a) b
  have := e (0, 0) (0, 0); have := e (0, 1) (0, 1); have := e (0, 0) (0, 1)
  have := e (1, 0) (1, 0); have := e (1, 1) (1, 1); have := e (1, 0) (1, 1)
  have := e (0, 0) (1, 0); have := e (0, 1) (1, 1); have := e (0, 0) (1, 1)
  simp [realProducts, symR, Fintype.sum_prod_type, Fin.sum_univ_three] at *
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp <;> linarith

theorem realProducts_symm (p : Fin 3 × Fin 3) : (realProducts p)ᵀ = realProducts p := by
  rcases p with ⟨i, j⟩
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [realProducts, symR]

/-- **`ε ⊗ ε` is symmetric and orthogonal to every product of symmetric operators**, and the ten
together are independent: the products span nine of the ten symmetric operators. -/
theorem realProducts_nine :
    Module.finrank ℝ (Submodule.span ℝ (Set.range realProducts)) = 9 ∧
      (epsR ⊗ₖ epsR)ᵀ = epsR ⊗ₖ epsR ∧
      (∀ p, ((epsR ⊗ₖ epsR) * realProducts p).trace = 0) ∧
      epsR ⊗ₖ epsR ∉ Submodule.span ℝ (Set.range realProducts) := by
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range realProducts)) = 9 := by
    rw [finrank_span_eq_card realProducts_linearIndependent]
    simp
  have horth : ∀ p, ((epsR ⊗ₖ epsR) * realProducts p).trace = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [realProducts, symR, epsR, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]
  refine ⟨hfin, ?_, horth, ?_⟩
  · ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [epsR]
  · intro hmem
    -- the trace pairing with `ε ⊗ ε` vanishes on the span but not on `ε ⊗ ε` itself
    have hlin : ∀ X ∈ Submodule.span ℝ (Set.range realProducts), ((epsR ⊗ₖ epsR) * X).trace = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx => obtain ⟨p, rfl⟩ := hx; exact horth p
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.trace_add, hx, hy, add_zero]
      | smul r x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
    have := hlin _ hmem
    simp [epsR, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at this

/-- **On `ℂ² ⊗ ℂ²` the products of Hermitian operators span all sixteen Hermitian operators**: each of the
sixteen observables is `±` a product of two Pauli matrices (`Elements/Observables.lean`: `obs_eq_pauli`). -/
theorem complexProducts_all :
    Submodule.span ℝ (Set.range fun p : Fin 4 × Fin 4 => pauli p.1 ⊗ₖ pauli p.2) = hermitian := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change (pauli a ⊗ₖ pauli b)ᴴ = pauli a ⊗ₖ pauli b
    rw [conjTranspose_kronecker, pauli_conjTranspose, pauli_conjTranspose]
  · rw [← span_obs_eq_hermitian, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [obs_eq_pauli]
    have hs : obsSign k = 1 ∨ obsSign k = -1 := by fin_cases k <;> simp [obsSign]
    have hm : pauli (obsA k) ⊗ₖ pauli (obsB k) ∈
        Submodule.span ℝ (Set.range fun p : Fin 4 × Fin 4 => pauli p.1 ⊗ₖ pauli p.2) :=
      Submodule.subset_span ⟨(obsA k, obsB k), rfl⟩
    rcases hs with h | h
    · rw [h, one_smul]; exact hm
    · rw [h, neg_one_smul]; exact Submodule.neg_mem _ hm

end Comparison.Article
