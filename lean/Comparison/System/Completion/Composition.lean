import Comparison.System.Completion.Numbers
import Comparison.System.Table.Hadrons
import Comparison.System.Table.Nuclei
import Comparison.Law.Rows
import Comparison.Law.Composite
import Comparison.GroupsContinuumLaw.Coupling
import Comparison.Article.Series
import Comparison.Article.Kaons
import Comparison.Article.Nuclei
import Comparison.Colour.Light

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 5: one composition (SI Props. 189, 191 to 198; Eqs. (48) to (50))

A composite is the law on the direct sum of its lines' words: with the meeting matrix `G`
(`G_ii = 1`, `G_ij = c_ij^{1/2}`) and the levels `D = diag(S_i)`, the level operator is `R = D^{1/2}GD^{1/2}` (the
spectrum of `GD`) and the shift is `Tr δ₁(R) = Σ_j δ₁(λ_j)`.

New here, for any number of lines: the law on the direct sum is the product over the normal modes,
`det(I − (GD) ⊗ X) = Π_j det(I − λ_jX)`, with Kronecker's rule `Tr[(GD) ⊗ X]^k = Tr R^k Tr X^k` and
`Tr R^k = Σ_j λ_j^k` (the spectral theorem for the real symmetric `R`); the composite walk `⊗_j B[λ_j]` (the
Kronecker product over the modes, on the words `κ → State`) is Perron with the product of the modes' roots; the second
order is `−(σ²/2)Σ_ij G_ij²S_iS_j`; for two lines `∂_{S₂}Tr(GD)^k|_{S₂=0} = ckS₁^{k−1}` (`k ≥ 2`) and `1` (`k = 1`), and
`Tr R^k = Tr(GD)^k` at every nonnegative level; the one-line reduction; the moved own clocks without the exterior files;
the available transitions' `31` moved transitions along another line; the triangle's `det G₃ = 1 − 3c + 2c^{3/2}cos φ` and the quarter-turn
positivity; the saturation `δ₁(S) → log(4/3)`.
-/

namespace Comparison.System.Completion.Comp

open Real Matrix Kronecker Filter Topology Comparison Comparison.Law

section Modes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The law on the direct sum splits over the modes, for any number of lines:** if `AP = P diag(l)` with `P`
invertible, then `det(I − A ⊗ M) = Π_j det(I − l_jM)`. -/
theorem kron_det_of_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix ι ι ℝ) (l : ι → ℝ) (hP : IsUnit P.det)
    (hAP : A * P = P * diagonal l) (M : Matrix n n ℝ) :
    (1 - A ⊗ₖ M).det = ∏ j, (1 - l j • M).det := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hA : A = P * diagonal l * P⁻¹ := by
    rw [← hAP, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  have hkron : 1 - A ⊗ₖ M = (P ⊗ₖ (1 : Matrix n n ℝ)) * (1 - diagonal l ⊗ₖ M) *
      (P⁻¹ ⊗ₖ (1 : Matrix n n ℝ)) := by
    rw [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hPinv, Matrix.one_kronecker_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hdet1 : (P ⊗ₖ (1 : Matrix n n ℝ)).det * (P⁻¹ ⊗ₖ (1 : Matrix n n ℝ)).det = 1 := by
    rw [← det_mul, ← Matrix.mul_kronecker_mul, hPinv, Matrix.one_mul, Matrix.one_kronecker_one,
      det_one]
  have hblock : (1 - diagonal l ⊗ₖ M : Matrix (ι × n) (ι × n) ℝ) =
      (blockDiagonal fun i : ι => 1 - l i • M).submatrix (Equiv.prodComm ι n)
        (Equiv.prodComm ι n) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.kroneckerMap_apply, diagonal_apply,
      Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply,
      Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      by_cases hk : k = k' <;> simp [hk]
    · simp [hij]
  rw [hkron, det_mul, det_mul, hblock, det_submatrix_equiv_self, det_blockDiagonal]
  linear_combination (∏ j, (1 - l j • M).det) * hdet1

/-- **`Tr A^k = Σ_j l_j^k`** when `AP = P diag(l)` with `P` invertible. -/
theorem trace_pow_of_eigen (A P : Matrix ι ι ℝ) (l : ι → ℝ) (hP : IsUnit P.det)
    (hAP : A * P = P * diagonal l) (k : ℕ) : (A ^ k).trace = ∑ j, l j ^ k := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hk : A ^ k * P = P * diagonal l ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hA : A ^ k = P * diagonal l ^ k * P⁻¹ := by
    rw [← hk, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  rw [hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPinv', Matrix.one_mul, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  all_goals simp [Pi.pow_apply]

/-- **Kronecker's rule for powers:** `(A ⊗ B)^k = A^k ⊗ B^k`. -/
theorem kron_pow {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix ι ι ℝ) (B : Matrix n n ℝ) (k : ℕ) :
    (A ⊗ₖ B) ^ k = (A ^ k) ⊗ₖ (B ^ k) := by
  induction k with
  | zero => simp [Matrix.one_kronecker_one]
  | succ k ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- **`Tr (AB)^k = Tr (BA)^k`.** -/
theorem trace_pow_mul_comm (A B : Matrix ι ι ℝ) (k : ℕ) : ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => simp
  | succ k =>
    have e : (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

/-- A real symmetric matrix commutes into its eigenvectors: `RU = U diag(λ)`. -/
theorem herm_eigen {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    R * (hR.eigenvectorUnitary : Matrix ι ι ℝ) =
      (hR.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hR.eigenvalues := by
  ext i j
  have h := congrFun (hR.mulVec_eigenvectorBasis j) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [h, mul_comm]

theorem herm_U_det {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    IsUnit (hR.eigenvectorUnitary : Matrix ι ι ℝ).det :=
  Matrix.isUnit_det_of_left_inverse (Unitary.coe_star_mul_self hR.eigenvectorUnitary)

/-- **The level operator** `R = D^{1/2}GD^{1/2}`. -/
noncomputable def levelR (G : Matrix ι ι ℝ) (S : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => √(S i)) * G * diagonal (fun i => √(S i))

theorem levelR_herm {G : Matrix ι ι ℝ} (hG : Gᵀ = G) (S : ι → ℝ) : (levelR G S).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, levelR, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.diagonal_transpose, hG, Matrix.mul_assoc]

/-- `GD = D^{−1/2}RD^{1/2}` for positive levels. -/
theorem GD_conj {G : Matrix ι ι ℝ} {S : ι → ℝ} (hS : ∀ i, 0 < S i) :
    G * diagonal S = diagonal (fun i => (√(S i))⁻¹) * levelR G S * diagonal (fun i => √(S i)) := by
  have h1 : diagonal (fun i => (√(S i))⁻¹) * diagonal (fun i => √(S i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hS i)).ne'
  have h2 : diagonal (fun i => √(S i)) * diagonal (fun i => √(S i)) = diagonal S := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hS i).le
  rw [levelR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2]

theorem GD_eigen {G : Matrix ι ι ℝ} (hG : Gᵀ = G) {S : ι → ℝ} (hS : ∀ i, 0 < S i) :
    G * diagonal S * (diagonal (fun i => (√(S i))⁻¹) * ((levelR_herm hG S).eigenvectorUnitary : Matrix ι ι ℝ)) =
      (diagonal (fun i => (√(S i))⁻¹) * ((levelR_herm hG S).eigenvectorUnitary : Matrix ι ι ℝ)) *
        diagonal (levelR_herm hG S).eigenvalues := by
  have h1 : diagonal (fun i => √(S i)) *
      (diagonal (fun i => (√(S i))⁻¹) * ((levelR_herm hG S).eigenvectorUnitary : Matrix ι ι ℝ)) =
      ((levelR_herm hG S).eigenvectorUnitary : Matrix ι ι ℝ) := by
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have : (fun i => √(S i) * (√(S i))⁻¹) = fun _ => (1 : ℝ) := by
      funext i
      exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hS i)).ne'
    rw [this, Matrix.diagonal_one, Matrix.one_mul]
  rw [GD_conj hS]
  simp only [Matrix.mul_assoc]
  rw [h1, herm_eigen (levelR_herm hG S)]

theorem P_det {G : Matrix ι ι ℝ} (hG : Gᵀ = G) {S : ι → ℝ} (hS : ∀ i, 0 < S i) :
    IsUnit (diagonal (fun i => (√(S i))⁻¹) * ((levelR_herm hG S).eigenvectorUnitary : Matrix ι ι ℝ)).det := by
  rw [det_mul]
  refine IsUnit.mul ?_ (herm_U_det (levelR_herm hG S))
  rw [det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    inv_ne_zero (Real.sqrt_pos.mpr (hS i)).ne')

/-- **Proposition 189 (iii), any number of lines:** `det(I − (GD) ⊗ X) = Π_j det(I − λ_jX)`. -/
theorem modes_det {G : Matrix ι ι ℝ} (hG : Gᵀ = G) {S : ι → ℝ} (hS : ∀ i, 0 < S i)
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    (1 - (G * diagonal S) ⊗ₖ X).det = ∏ j, (1 - (levelR_herm hG S).eigenvalues j • X).det :=
  kron_det_of_eigen _ _ _ (P_det hG hS) (GD_eigen hG hS) X

/-- **Proposition 189 (iii), the traces:** `Tr[(GD) ⊗ X]^k = Tr R^k Tr X^k` and `Tr R^k = Σ_j λ_j^k`. -/
theorem modes_trace {G : Matrix ι ι ℝ} (hG : Gᵀ = G) {S : ι → ℝ} (hS : ∀ i, 0 < S i)
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) (k : ℕ) :
    (((G * diagonal S) ⊗ₖ X) ^ k).trace = ((levelR G S) ^ k).trace * (X ^ k).trace ∧
      ((levelR G S) ^ k).trace = ∑ j, (levelR_herm hG S).eigenvalues j ^ k := by
  have h1 := trace_pow_of_eigen _ _ _ (P_det hG hS) (GD_eigen hG hS) k
  have h2 := trace_pow_of_eigen _ _ _ (herm_U_det (levelR_herm hG S)) (herm_eigen (levelR_herm hG S)) k
  refine ⟨?_, h2⟩
  rw [kron_pow, Matrix.trace_kronecker, h1, h2]

/-- **Proposition 189 (iv), any number of lines:** with `G_ii = 1`, the modes' second-order polynomial is
`Σ_iS_i/5 − (6/125)Σ_ij G_ij²S_iS_j`. -/
theorem modes_second_order {G : Matrix ι ι ℝ} (hG : Gᵀ = G) (hd : ∀ i, G i i = 1) {S : ι → ℝ}
    (hS : ∀ i, 0 ≤ S i) :
    ∑ j, ((levelR_herm hG S).eigenvalues j / 5 - 6 / 125 * (levelR_herm hG S).eigenvalues j ^ 2) =
      (∑ i, S i) / 5 - 6 / 125 * ∑ i, ∑ j, G i j ^ 2 * S i * S j := by
  have hR := levelR_herm hG S
  have h1 := trace_pow_of_eigen _ _ _ (herm_U_det (levelR_herm hG S)) (herm_eigen (levelR_herm hG S)) 1
  have h2 := trace_pow_of_eigen _ _ _ (herm_U_det (levelR_herm hG S)) (herm_eigen (levelR_herm hG S)) 2
  simp only [pow_one] at h1
  have hsq : ∀ i, √(S i) * √(S i) = S i := fun i => Real.mul_self_sqrt (hS i)
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j
    simpa [Matrix.transpose_apply] using this
  have t1 : (levelR G S).trace = ∑ i, S i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, levelR, Matrix.mul_diagonal, Matrix.diagonal_mul, hd, mul_one, hsq]
  have t2 : (levelR G S ^ 2).trace = ∑ i, ∑ j, G i j ^ 2 * S i * S j := by
    rw [sq, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [levelR, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, hsym i j]
    calc √(S i) * G i j * √(S j) * (√(S j) * G i j * √(S i))
        = (√(S i) * √(S i)) * (√(S j) * √(S j)) * G i j ^ 2 := by ring
      _ = G i j ^ 2 * S i * S j := by rw [hsq, hsq]; ring
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← h1, ← h2, t1, t2]

/-- **The composite walk** `⊗_j B_j` on the words `κ → State`: `(⊗_j B_j)(x, y) = Π_j B_j(x_j, y_j)`. -/
def kronPi {κ : Type*} [Fintype κ] (B : κ → Matrix State State ℝ) : Matrix (κ → State) (κ → State) ℝ :=
  Matrix.of fun x y => ∏ j, B j (x j) (y j)

theorem kronPi_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ] (B : κ → Matrix State State ℝ)
    (v : κ → State → ℝ) :
    kronPi B *ᵥ (fun x => ∏ j, v j (x j)) = fun x => ∏ j, (B j *ᵥ v j) (x j) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, kronPi, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kronPi_vecMul {κ : Type*} [Fintype κ] [DecidableEq κ] (B : κ → Matrix State State ℝ)
    (w : κ → State → ℝ) :
    (fun x => ∏ j, w j (x j)) ᵥ* kronPi B = fun y => ∏ j, (w j ᵥ* B j) (y j) := by
  funext y
  simp only [Matrix.vecMul, dotProduct, kronPi, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]

/-- **The composite walk is Perron with the product of the modes' roots.** -/
theorem kronPi_isPerron {κ : Type*} [Fintype κ] [DecidableEq κ] (B : κ → Matrix State State ℝ)
    (ρ : κ → ℝ) (hB : ∀ j a b, 0 ≤ B j a b) (hP : ∀ j, IsPerron (B j) (ρ j)) :
    IsPerron (kronPi B) (∏ j, ρ j) := by
  have hr : ∀ j, 0 < ρ j := fun j => (hP j).1
  choose x hx hMx using fun j => (hP j).2.1
  choose y hy hyM using fun j => (hP j).2.2.1
  refine isPerron_of_pos (kronPi B) (fun a b => ?_) _ (Finset.prod_pos fun j _ => hr j)
    (fun a => ∏ j, x j (a j)) (fun a => ∏ j, y j (a j)) (fun a => Finset.prod_pos fun j _ => hx j _)
    (fun a => Finset.prod_pos fun j _ => hy j _) ?_ ?_
  · simp only [kronPi, Matrix.of_apply]
    exact Finset.prod_nonneg fun j _ => hB j _ _
  · rw [kronPi_mulVec]
    funext a
    simp only [hMx, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  · rw [kronPi_vecMul]
    funext a
    simp only [hyM, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

theorem lastDirectionWalk_nonneg (h : Fin 5) (s : ℝ) (a b : State) : 0 ≤ lastDirectionWalk h s a b := by
  simp only [lastDirectionWalk, Matrix.smul_apply, stepT, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> positivity

/-- **Proposition 189 (ii):** the composite walk `⊗_j B[λ_j]` of the modes is Perron with the root
`ρ = Π_j λ(λ_j)/4`, and its zero shift is `−log ρ = Σ_j δ₁(λ_j)`. -/
theorem composite_walk {κ : Type*} [Fintype κ] [DecidableEq κ] (h : Fin 5) (lam : κ → ℝ) :
    IsPerron (kronPi fun j => lastDirectionWalk h (-lam j)) (∏ j, lamLevel (lam j) / 4) ∧
      -Real.log (∏ j, lamLevel (lam j) / 4) = ∑ j, deltaLevel (lam j) := by
  refine ⟨kronPi_isPerron _ _ (fun j => lastDirectionWalk_nonneg h _) (fun j => level_perron h (lam j)), ?_⟩
  rw [Real.log_prod (fun j _ => (div_pos (lamLevel_pos (lam j)) (by norm_num)).ne'), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (Law.deltaLevel_eq (lam j)).symm

end Modes

/-! ## Two lines -/

/-- `GD = [[1, g], [g, 1]] diag(S₁, S₂)`. -/
theorem levelOp_eq (S₁ S₂ g : ℝ) : levelOp S₁ S₂ g = !![1, g; g, 1] * diagonal ![S₁, S₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levelOp, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`Tr R^k = Tr(GD)^k` at every nonnegative level** (the trace's cyclicity; no inverse needed). -/
theorem trace_R_eq_GD (S₁ S₂ g : ℝ) (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) (k : ℕ) :
    ((levelR !![1, g; g, 1] ![S₁, S₂]) ^ k).trace = ((levelOp S₁ S₂ g) ^ k).trace := by
  have hD : diagonal (fun i => √(![S₁, S₂] i)) * diagonal (fun i => √(![S₁, S₂] i)) = diagonal ![S₁, S₂] := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · exact Real.mul_self_sqrt h₁
    · exact Real.mul_self_sqrt h₂
  rw [levelOp_eq, ← hD, levelR, Matrix.mul_assoc, ← Matrix.mul_assoc (!![1, g; g, 1]),
    trace_pow_mul_comm]

theorem levelOp_sq (S₁ S₂ g : ℝ) :
    levelOp S₁ S₂ g * levelOp S₁ S₂ g =
      (S₁ + S₂) • levelOp S₁ S₂ g - ((1 - g ^ 2) * S₁ * S₂) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levelOp, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Newton's recursion for the two lines: `p_{k+2} = (S₁ + S₂)p_{k+1} − (1 − c)S₁S₂p_k`. -/
theorem trace_level_rec (S₁ S₂ g : ℝ) (k : ℕ) :
    ((levelOp S₁ S₂ g) ^ (k + 2)).trace =
      (S₁ + S₂) * ((levelOp S₁ S₂ g) ^ (k + 1)).trace -
        (1 - g ^ 2) * S₁ * S₂ * ((levelOp S₁ S₂ g) ^ k).trace := by
  have e1 : (levelOp S₁ S₂ g) ^ (k + 2) = (levelOp S₁ S₂ g) ^ k * (levelOp S₁ S₂ g * levelOp S₁ S₂ g) := by
    rw [pow_add, pow_two]
  have e2 : (levelOp S₁ S₂ g) ^ (k + 1) = (levelOp S₁ S₂ g) ^ k * levelOp S₁ S₂ g := pow_succ _ _
  rw [e1, levelOp_sq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← e2,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

theorem trace_level_at_zero (S₁ g : ℝ) :
    ∀ k : ℕ, ((levelOp S₁ 0 g) ^ (k + 1)).trace = S₁ ^ (k + 1) ∧
      ((levelOp S₁ 0 g) ^ (k + 2)).trace = S₁ ^ (k + 2) := by
  have h1 : ((levelOp S₁ 0 g) ^ 1).trace = S₁ := by
    rw [pow_one, Matrix.trace_fin_two]
    simp [levelOp]
  intro k
  induction k with
  | zero =>
    refine ⟨by rw [h1]; ring, ?_⟩
    rw [trace_level_rec, h1]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 2 = k + 1 + 1 + 1 by ring, trace_level_rec, show k + 1 + 1 = k + 2 by ring, ih.2]
    ring

/-- **Proposition 189 (v), the terms linear in one level:** `∂_{S₂}Tr(GD)^k|_{S₂=0} = 1` for `k = 1` and
`= ckS₁^{k−1}` for `k ≥ 2`, `c = g²`. -/
theorem trace_level_deriv (S₁ g : ℝ) :
    HasDerivAt (fun t => ((levelOp S₁ t g) ^ 1).trace) 1 0 ∧
      ∀ k : ℕ, HasDerivAt (fun t => ((levelOp S₁ t g) ^ (k + 2)).trace) (g ^ 2 * (k + 2) * S₁ ^ (k + 1)) 0 := by
  -- the traces as functions of `t = S₂`
  have f0 : (fun t => ((levelOp S₁ t g) ^ 0).trace) = fun _ => (2 : ℝ) := by
    funext t
    simp
  have f1 : (fun t => ((levelOp S₁ t g) ^ 1).trace) = fun t => S₁ + t := by
    funext t
    rw [pow_one, Matrix.trace_fin_two]
    simp [levelOp]
  have d0 : HasDerivAt (fun t => ((levelOp S₁ t g) ^ 0).trace) 0 0 := by
    rw [f0]; exact hasDerivAt_const _ _
  have d1 : HasDerivAt (fun t => ((levelOp S₁ t g) ^ 1).trace) 1 0 := by
    rw [f1]; simpa using (hasDerivAt_id (0 : ℝ)).const_add S₁
  -- the recursion's derivative
  have step : ∀ (m : ℕ) (Dm Dm1 : ℝ),
      HasDerivAt (fun t => ((levelOp S₁ t g) ^ m).trace) Dm 0 →
      HasDerivAt (fun t => ((levelOp S₁ t g) ^ (m + 1)).trace) Dm1 0 →
      HasDerivAt (fun t => ((levelOp S₁ t g) ^ (m + 2)).trace)
        (((levelOp S₁ 0 g) ^ (m + 1)).trace + S₁ * Dm1 - (1 - g ^ 2) * S₁ * ((levelOp S₁ 0 g) ^ m).trace) 0 := by
    intro m Dm Dm1 hm hm1
    have e : (fun t => ((levelOp S₁ t g) ^ (m + 2)).trace) =
        fun t => (S₁ + t) * ((levelOp S₁ t g) ^ (m + 1)).trace -
          (1 - g ^ 2) * S₁ * t * ((levelOp S₁ t g) ^ m).trace := by
      funext t
      rw [trace_level_rec]
    rw [e]
    have ha := ((hasDerivAt_id (0 : ℝ)).const_add S₁).mul hm1
    have hb := ((hasDerivAt_id (0 : ℝ)).const_mul ((1 - g ^ 2) * S₁)).mul hm
    convert ha.sub hb using 1
    · funext t
      simp only [Pi.mul_apply, Pi.sub_apply, id]
    · simp only [id]
      ring
  have z := trace_level_at_zero S₁ g
  refine ⟨d1, fun k => ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · -- `k + 2 = 2`
      have h2 := step 0 0 1 d0 d1
      convert h2 using 1
      rw [(z 0).1, pow_zero, Matrix.trace_one]
      simp
      ring
    · rcases k with _ | k
      · -- `k + 2 = 3`
        have h3 := step 1 1 (g ^ 2 * (0 + 2) * S₁ ^ (0 + 1)) d1 (by simpa using ih 0 (by omega))
        convert h3 using 1
        rw [(z 1).1, (z 0).1]
        push_cast
        ring
      · -- `k + 2 = k + 4`
        have hA := ih k (by omega)
        have hB := ih (k + 1) (by omega)
        have h := step (k + 2) _ _ hA (by simpa [show k + 1 + 2 = k + 2 + 1 by ring] using hB)
        convert h using 2
        · rw [(z (k + 2)).1, (z (k + 1)).1]
          push_cast
          ring

/-- **Proposition 191: one line.** With one level zero `R` has the spectrum `{S, 0}`, so `Tr δ₁(R) = δ₁(S)` at every
coupling. -/
theorem one_line (S c : ℝ) (hS : 0 ≤ S) : compositeDelta S 0 c = deltaLevel S := by
  have hd : discR S 0 c = S := by
    rw [discR, show (S - 0) ^ 2 + 4 * c * S * 0 = S ^ 2 by ring, Real.sqrt_sq hS]
  rw [compositeDelta, eigenPlus, eigenMinus, hd, show (S + 0 + S) / 2 = S by ring,
    show (S + 0 - S) / 2 = 0 by ring, deltaLevel_zero, add_zero]

/-- The own clocks a division `D` of the six moves: the lines `t` whose plane with the singlet it crosses. -/
def movedOwn (D : Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ.filter fun t => t ≠ 0 ∧ movesTurn D 0 t = true

/-- **The moved own clocks at the six divisions a line holds:** none at `{}`, all five at `{n}`, the four other
lines at `{h, n}`, `h` at `{h}`, `h, k` at `F`, the colour lines at `C`. -/
theorem moved_own_clocks :
    movedOwn ∅ = ∅ ∧ movedOwn {0} = {1, 2, 3, 4, 5} ∧ movedOwn {0, 1} = {2, 3, 4, 5} ∧
      movedOwn {1} = {1} ∧ movedOwn {1, 2} = {1, 2} ∧ movedOwn {3, 4, 5} = {3, 4, 5} := by
  decide

/-- **The same for every last-step direction `h` and previous-step direction `k`.** -/
theorem moved_own_every_lastDirection : ∀ h k : Fin 5, h ≠ k →
    movedOwn ∅ = ∅ ∧ movedOwn {0} = Finset.univ.erase 0 ∧
      movedOwn {0, h.succ} = (Finset.univ.erase 0).erase h.succ ∧ movedOwn {h.succ} = {h.succ} ∧
      movedOwn {h.succ, k.succ} = {h.succ, k.succ} ∧
      movedOwn (Finset.univ \ {0, h.succ, k.succ}) = Finset.univ \ {0, h.succ, k.succ} := by
  decide +kernel

/-- **The available transitions along `h`:** four at each two-spinor state other than the singlet, with or without the record
`(T_h, h)`; the singlet is outside the available transitions (the first step out of it is not a transition). -/
theorem availableTransitions_transitions_per_relation : ∀ (h : Fin 5) (U : Fin 16), U ≠ 0 →
    (Finset.univ.filter fun p : State × State =>
      p.1.1 = U ∧ inExcursion h p.1 = true ∧ Continues p.1 p.2 ∧ p.2.2 = h).card = 4 := by
  decide +kernel

theorem availableTransitions_record_transitions_per_relation : ∀ (h : Fin 5) (U : Fin 16), U ≠ 0 →
    (Finset.univ.filter fun p : State × State =>
      p.1.1 = U ∧ (inExcursion h p.1 = true ∨ p.1 = (lastDirectionRel h, h)) ∧ Continues p.1 p.2 ∧ p.2.2 = h).card = 4 := by
  decide +kernel

theorem singlet_outside_availableTransitions : ∀ h t : Fin 5, inExcursion h (0, t) = false := by
  decide

/-- The line of an index of the six (`0` is the singlet; its value there is not used). -/
def lineOf (b : Fin 6) : Fin 5 := if h : b = 0 then 0 else b.pred h

/-- **The two-spinor state's own rotation** `X_S`: `1` at the singlet, the clock `iγ_t` at the vector state `T_t`, the plane's rotation
`γ_aγ_b` at a plane, read off `relTurn`. -/
noncomputable def turnOp (U : Fin 16) : Matrix Four Four ℂ :=
  if (relTurn U).1 = 0 then (if (relTurn U).2 = 0 then 1 else Complex.I • γ (lineOf (relTurn U).2))
  else γ (lineOf (relTurn U).1) * γ (lineOf (relTurn U).2)

/-- The two-spinor state's own rotation is the two-spinor state's operator at the singlet and the symmetric states, and `i` times it at the five vector
states. -/
theorem turnOp_cases : ∀ U : Fin 16, turnOp U = relOp U ∨ turnOp U = Complex.I • relOp U := by
  intro U
  fin_cases U
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- **`e_S = (X_S ⊗ 1)Ω` up to a phase:** the phase is `1` at the singlet and the symmetric states and `−i` at the vector states. -/
theorem rel_eq_turn : ∀ U : Fin 16, ∃ c : ℂ, ‖c‖ = 1 ∧ rel U = c • ((turnOp U ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) := by
  intro U
  rcases turnOp_cases U with h | h
  · refine ⟨1, by simp, ?_⟩
    rw [h, one_smul]
    rfl
  · refine ⟨-Complex.I, by simp, ?_⟩
    rw [h, Matrix.smul_kronecker, Matrix.smul_mulVec, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rfl

/-- **The available transitions along another line:** of its `59` transitions along `j ≠ h`, `31` stand where the two-spinor state moves `(n j)`;
with the record `(T_h, h)`, `60` and `32` for every line. -/
theorem availableTransitions_moved_other : ∀ h j : Fin 5, j ≠ h →
    ((excursionStates h).filter fun s => s.2 ≠ j ∧ j ∈ disagreeSet s.1).card = 31 := by
  decide +kernel

theorem availableTransitions_moved_record : ∀ h j : Fin 5,
    (Finset.univ.filter fun s : State =>
      (inExcursion h s = true ∨ s = (lastDirectionRel h, h)) ∧ s.2 ≠ j ∧ j ∈ disagreeSet s.1).card = 32 := by
  decide +kernel

/-- **The triangle of three lines:** `det G₃ = 1 − 3g² + 2g³cos φ` with `φ = φ₁₂ + φ₂₃ − φ₁₃`. -/
theorem det_triangle (g a b d : ℝ) :
    (!![(1 : ℂ), g * Complex.exp (a * Complex.I), g * Complex.exp (d * Complex.I);
        g * Complex.exp (-(a : ℂ) * Complex.I), 1, g * Complex.exp (b * Complex.I);
        g * Complex.exp (-(d : ℂ) * Complex.I), g * Complex.exp (-(b : ℂ) * Complex.I), 1]).det =
      ((1 - 3 * g ^ 2 + 2 * g ^ 3 * Real.cos (a + b - d) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hc : ((1 - 3 * g ^ 2 + 2 * g ^ 3 * Real.cos (a + b - d) : ℝ) : ℂ) =
      1 - 3 * (g : ℂ) ^ 2 + (g : ℂ) ^ 3 * ((2 * Real.cos (a + b - d) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc]
  have e1 : Complex.exp (a * Complex.I) * Complex.exp (-(a : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have e2 : Complex.exp (b * Complex.I) * Complex.exp (-(b : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have e3 : Complex.exp (d * Complex.I) * Complex.exp (-(d : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have e4 : Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I) * Complex.exp (-(d : ℂ) * Complex.I) =
      Complex.exp (((a + b - d : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have e5 : Complex.exp (-(a : ℂ) * Complex.I) * Complex.exp (-(b : ℂ) * Complex.I) * Complex.exp (d * Complex.I) =
      Complex.exp (-(((a + b - d : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have e6 : Complex.exp (((a + b - d : ℝ) : ℂ) * Complex.I) + Complex.exp (-(((a + b - d : ℝ) : ℂ)) * Complex.I) =
      ((2 * Real.cos (a + b - d) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cos]
    rw [Complex.cos]
    push_cast
    ring_nf
  linear_combination (-(g : ℂ) ^ 2) * e1 + (-(g : ℂ) ^ 2) * e2 + (-(g : ℂ) ^ 2) * e3 + (g : ℂ) ^ 3 * e4 +
    (g : ℂ) ^ 3 * e5 + (g : ℂ) ^ 3 * e6

/-- **Positivity keeps only the flat triangle among the quarter-turn phases:** at `c = 8/15`,
`1 − 3c + 2c^{3/2}cos φ` is positive at `φ = 0` and negative at `φ = π/2, π, 3π/2`. -/
theorem quarter_turn_positivity :
    (0 : ℝ) < 1 - 3 * (8 / 15) + 2 * (8 / 15) * √(8 / 15) * Real.cos 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos (π / 2) < 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos π < 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos (3 * π / 2) < 0 := by
  have hs : (0.73 : ℝ) < √(8 / 15) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs1 : √(8 / 15) < (0.7303 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have c3 : Real.cos (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.cos_zero]; nlinarith
  · rw [Real.cos_pi_div_two]; norm_num
  · rw [Real.cos_pi]; nlinarith [Real.sqrt_nonneg (8 / 15 : ℝ)]
  · rw [c3]; norm_num

/-- **A positive level saturates at `log(4/3)`:** `δ₁(S) < log(4/3)` and `δ₁(S) → log(4/3)` as `S → ∞`; the two roots
`r_± = (3 ± (9 + 16e^{−S})^{1/2})/8` solve `4r² − 3r − e^{−S} = 0`, and `δ₁ = −log r₊`. -/
theorem level_saturation :
    (∀ S : ℝ, deltaLevel S < Real.log (4 / 3)) ∧ Tendsto deltaLevel atTop (𝓝 (Real.log (4 / 3))) ∧
      (∀ S : ℝ, 4 * ((3 + √(9 + 16 * Real.exp (-S))) / 8) ^ 2 - 3 * ((3 + √(9 + 16 * Real.exp (-S))) / 8) -
          Real.exp (-S) = 0 ∧
        4 * ((3 - √(9 + 16 * Real.exp (-S))) / 8) ^ 2 - 3 * ((3 - √(9 + 16 * Real.exp (-S))) / 8) -
          Real.exp (-S) = 0 ∧
        deltaLevel S = -Real.log ((3 + √(9 + 16 * Real.exp (-S))) / 8)) := by
  have hq : ∀ S : ℝ, √(9 + 16 * Real.exp (-S)) ^ 2 = 9 + 16 * Real.exp (-S) := fun S =>
    Real.sq_sqrt (by positivity)
  refine ⟨fun S => ?_, ?_, fun S => ⟨?_, ?_, level_value S⟩⟩
  · rw [level_value, ← Real.log_inv]
    have h3 : 3 < √(9 + 16 * Real.exp (-S)) := by
      rw [Real.lt_sqrt (by norm_num)]
      have := Real.exp_pos (-S)
      linarith
    apply Real.log_lt_log (by positivity)
    rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · have hc : ContinuousAt (fun x : ℝ => -Real.log ((3 + √(9 + 16 * x)) / 8)) 0 := by
      refine (ContinuousAt.log ?_ ?_).neg
      · exact ((continuousAt_const.add (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.add (continuousAt_const.mul continuousAt_id)))).div_const 8)
      · simp
        positivity
    have ht := hc.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    have hv : -Real.log ((3 + √(9 + 16 * (0 : ℝ))) / 8) = Real.log (4 / 3) := by
      rw [show (9 + 16 * (0 : ℝ)) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), ← Real.log_inv]
      norm_num
    rw [hv] at ht
    refine ht.congr fun S => ?_
    simp only [Function.comp]
    rw [level_value]
  · nlinarith [hq S]
  · nlinarith [hq S]

end Comparison.System.Completion.Comp

namespace Comparison.System

open Real Matrix Kronecker Filter Topology Asymptotics Comparison Comparison.Law Comparison.System.Completion

/-- **Proposition 189 (the one composition: the law on the spectrum of the level operator).** On the direct sum of
the lines' words, with `G` real symmetric (`G_ii = 1`), `D = diag(S_i)`, `S_i > 0`, and `R = D^{1/2}GD^{1/2}` with its
eigenvalues `λ_j` (the spectrum of `GD`): (iii) the law on the direct sum is the product over the modes,
`det(I − (GD) ⊗ X) = Π_j det(I − λ_jX)` for every square `X` (as `K⁻¹J`), and `Tr[(GD) ⊗ X]^k = Tr R^k Tr X^k`,
`Tr R^k = Σ_jλ_j^k`; (ii) the composite walk `⊗_jB[λ_j]` is Perron with root `ρ = Π_jλ(λ_j)/4` and zero shift
`−log ρ = Σ_jδ₁(λ_j)`; (iv) the second order is `−(σ²/2)Σ_ij G_ij²S_iS_j`, `σ² = 12/125`; (i) `G = I` gives the line
side and `G = 𝟏𝟏ᵀ` the meeting side; (v) for two lines `Tr R³ = (1 − c)(S₁³ + S₂³) + c(S₁ + S₂)³`, `Tr R^k = Tr(GD)^k`
at every nonnegative level, `∂_{S₂}Tr(GD)^k|_{S₂=0} = ckS₁^{k−1}` for `k ≥ 2` and `1` for `k = 1`, and the first
difference from `(1 − c)δ_L + cδ_M` is `−2c(1 − c)d₄S₁²S₂²`.

Recognition: a meson's mass squared `m² = L(Ω)m_p²δ` (the theory's composition rule, C); Gell-Mann, Oakes and Renner
at first order. -/
theorem prop_189 :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : Gᵀ = G) (S : ι → ℝ), (∀ i, 0 < S i) →
      ∀ {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ),
        (1 - (G * diagonal S) ⊗ₖ X).det = ∏ j, (1 - (Comp.levelR_herm hG S).eigenvalues j • X).det ∧
        ∀ k : ℕ, (((G * diagonal S) ⊗ₖ X) ^ k).trace = ((Comp.levelR G S) ^ k).trace * (X ^ k).trace ∧
          ((Comp.levelR G S) ^ k).trace = ∑ j, (Comp.levelR_herm hG S).eigenvalues j ^ k) ∧
    (∀ {κ : Type} [Fintype κ] [DecidableEq κ] (h : Fin 5) (lam : κ → ℝ),
      IsPerron (Comp.kronPi fun j => lastDirectionWalk h (-lam j)) (∏ j, lamLevel (lam j) / 4) ∧
        -Real.log (∏ j, lamLevel (lam j) / 4) = ∑ j, deltaLevel (lam j)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : Gᵀ = G), (∀ i, G i i = 1) →
      ∀ S : ι → ℝ, (∀ i, 0 ≤ S i) →
        ∑ j, ((Comp.levelR_herm hG S).eigenvalues j / 5 - 6 / 125 * (Comp.levelR_herm hG S).eigenvalues j ^ 2) =
          (∑ i, S i) / 5 - (12 / 125) / 2 * ∑ i, ∑ j, G i j ^ 2 * S i * S j) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (M : Matrix n n ℝ),
      (1 - levelOp S₁ S₂ 0 ⊗ₖ M).det = (1 - S₁ • M).det * (1 - S₂ • M).det) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ), S₂ ≠ 0 → S₁ + S₂ ≠ 0 → ∀ M : Matrix n n ℝ,
      (1 - levelOp S₁ S₂ 1 ⊗ₖ M).det = (1 - (S₁ + S₂) • M).det) ∧
    (∀ S₁ S₂ c : ℝ, 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂ →
      eigenPlus S₁ S₂ c ^ 3 + eigenMinus S₁ S₂ c ^ 3 = (1 - c) * (S₁ ^ 3 + S₂ ^ 3) + c * (S₁ + S₂) ^ 3) ∧
    (∀ (S₁ S₂ g : ℝ), 0 ≤ S₁ → 0 ≤ S₂ → ∀ k : ℕ,
      ((Comp.levelR !![1, g; g, 1] ![S₁, S₂]) ^ k).trace = ((levelOp S₁ S₂ g) ^ k).trace) ∧
    (∀ S₁ g : ℝ, HasDerivAt (fun t => ((levelOp S₁ t g) ^ 1).trace) 1 0 ∧
      ∀ k : ℕ, HasDerivAt (fun t => ((levelOp S₁ t g) ^ (k + 2)).trace) (g ^ 2 * (k + 2) * S₁ ^ (k + 1)) 0) ∧
    (∀ S₁ S₂ c d4 : ℝ, 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂ →
      Article.levelT4 d4 (eigenPlus S₁ S₂ c) + Article.levelT4 d4 (eigenMinus S₁ S₂ c) -
          ((1 - c) * (Article.levelT4 d4 S₁ + Article.levelT4 d4 S₂) + c * Article.levelT4 d4 (S₁ + S₂)) =
        -2 * c * (1 - c) * d4 * S₁ ^ 2 * S₂ ^ 2) ∧
    (iteratedDeriv 4 deltaLevel 0 / 24 = 43 / 31250) := by
  refine ⟨?_, fun h lam => Comp.composite_walk h lam, fun G hG hd S hS => ?_,
    fun S₁ S₂ M => line_side_det S₁ S₂ M, fun S₁ S₂ hS hT M => meeting_side_det S₁ S₂ hS hT M,
    fun S₁ S₂ c hd => eigen_cube S₁ S₂ c hd, fun S₁ S₂ g h₁ h₂ k => Comp.trace_R_eq_GD S₁ S₂ g h₁ h₂ k,
    fun S₁ g => Comp.trace_level_deriv S₁ g, fun S₁ S₂ c d4 hd => Article.fourth_order_difference S₁ S₂ c d4 hd,
    Article.level_taylor.2.2.2.2.1⟩
  · intro ι _ _ G hG S hS n _ _ X
    exact ⟨Comp.modes_det hG hS X, fun k => Comp.modes_trace hG hS X k⟩
  · rw [Comp.modes_second_order hG hd hS]
    ring

/-- **Proposition 191 (what the composition requires).** The coupling enters only at the second order and in the
terms linear in one level, never at first order (`λ₊ + λ₋ = S₁ + S₂` at every `c`); the first pairing writes `c = 0`
(the line side, `δ₁(S₁) + δ₁(S₂)`) and the second `c = 1` (the meeting side, `δ₁(S₁ + S₂)`); for one line,
`Tr δ₁(R) = δ₁(S)` at every coupling.

Recognition (C): `c_ij = G_ij²` is the share of a bound state's clock transitions at which the clocks of its lines `i` and `j`
are one rotation (Prop. 194). -/
theorem prop_191 :
    (∀ S₁ S₂ c : ℝ, eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c = S₁ + S₂) ∧
    (∀ S₁ S₂ : ℝ, 0 ≤ S₁ → 0 ≤ S₂ →
      compositeDelta S₁ S₂ 0 = deltaLevel S₁ + deltaLevel S₂ ∧ compositeDelta S₁ S₂ 1 = deltaLevel (S₁ + S₂)) ∧
    (∀ S c : ℝ, 0 ≤ S → compositeDelta S 0 c = deltaLevel S) :=
  ⟨eigen_sum, composite_ends, fun S c hS => Comp.one_line S c hS⟩

/-- **Proposition 192 (the meeting moves a line's clock at eight of the fifteen two-spinor states).** The two-spinor state's own rotation
is the plane's rotation `(ab)` for a plane `{a, b}` and the clock `(n t)` (the singlet with the missing line) for a vector
state; `θ_S` moves `(n r)` exactly when `r ∈ S`, exactly when `r`'s time division `{r, n}` moves the two-spinor state's
rotation: at `8` of the `15` two-spinor states other than the singlet, for every line `r`; `{r, n}` moves `8` and keeps `7` of the
`15` rotations of the six; the own clocks moved by the six divisions a line holds are none at `{}`, all five at `{n}`,
`k, c₁, c₂, c₃` at `{h, n}`, `h` at `{h}`, `h, k` at `F` and `c₁, c₂, c₃` at `C`, for every last-step direction `h` and previous-step direction `k`;
and each two-spinor state is its own rotation on the singlet, `e_S = c(X_S ⊗ 1)Ω` with `|c| = 1`, `X_S = γ_aγ_b` at a plane and
`iγ_t` at the vector state `T_t`. -/
theorem prop_192 :
    (∀ U : Fin 16, U ≠ 0 →
      ((disagreeSet U).card = 2 → relDiv U = {(relTurn U).1, (relTurn U).2}) ∧
        ((disagreeSet U).card = 4 → (relTurn U).1 = 0 ∧ (relTurn U).2 ∉ relDiv U)) ∧
    (∀ (r : Fin 5) (U : Fin 16), movesTurn (relDiv U) 0 r.succ = decide (r ∈ disagreeSet U)) ∧
    (∀ (r : Fin 5) (U : Fin 16), U ≠ 0 →
      movesTurn {0, r.succ} (relTurn U).1 (relTurn U).2 = decide (r ∈ disagreeSet U)) ∧
    (∀ r : Fin 5, (Finset.univ.filter fun U : Fin 16 => U ≠ 0 ∧ r ∈ disagreeSet U).card = 8) ∧
    (∀ r : Fin 5,
      (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = true).card = 8 ∧
        (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = false).card = 7) ∧
    (Comp.movedOwn ∅ = ∅ ∧ Comp.movedOwn {0} = {1, 2, 3, 4, 5} ∧ Comp.movedOwn {0, 1} = {2, 3, 4, 5} ∧
      Comp.movedOwn {1} = {1} ∧ Comp.movedOwn {1, 2} = {1, 2} ∧ Comp.movedOwn {3, 4, 5} = {3, 4, 5}) ∧
    (∀ h k : Fin 5, h ≠ k →
      Comp.movedOwn ∅ = ∅ ∧ Comp.movedOwn {0} = Finset.univ.erase 0 ∧
        Comp.movedOwn {0, h.succ} = (Finset.univ.erase 0).erase h.succ ∧ Comp.movedOwn {h.succ} = {h.succ} ∧
        Comp.movedOwn {h.succ, k.succ} = {h.succ, k.succ} ∧
        Comp.movedOwn (Finset.univ \ {0, h.succ, k.succ}) = Finset.univ \ {0, h.succ, k.succ}) ∧
    (∀ U : Fin 16, ∃ c : ℂ, ‖c‖ = 1 ∧ rel U = c • ((Comp.turnOp U ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω)) :=
  ⟨relTurn_spec, prop192_moves, relTurn_moved, prop192_count, time_division_turns, Comp.moved_own_clocks,
    Comp.moved_own_every_lastDirection, Comp.rel_eq_turn⟩

/-- **Proposition 193 (the bound state's transitions).** The walk's `64` steps along `r` per stationary cycle of `320` are four
at each of the sixteen two-spinor states; the available transitions of `h` have `60` transitions along `h`, four at each two-spinor state other than the
singlet, `32` where the two-spinor state moves `(n h)`; along another line `59` transitions, `31` moved; with the record `(T_h, h)`
every line is alike: `60` transitions, `32` moved; the available transitions along `h` are four at each two-spinor state other than the
singlet (with or without the record), and the singlet is outside the available transitions, so the first step out of the singlet is not an
available transition; per excursion `Eℓ/5 = 16/5` steps along `h`, of which `(Eℓ − 1)/5 = C_h/20 = E_H = 3` are available transitions. -/
theorem prop_193 :
    (∀ j : Fin 5, (arcs.filter fun b => b.2.2 = j).card = 64) ∧
    (∀ (r : Fin 5) (U : Fin 16),
      (Finset.univ.filter fun p : State × State => p.1.1 = U ∧ Continues p.1 p.2 ∧ p.2.2 = r).card = 4) ∧
    (∀ h : Fin 5, alongCount h h = 60 ∧ ∀ j, j ≠ h → alongCount h j = 59) ∧
    (∀ h : Fin 5, ∑ s : State, ∑ s' : State,
      (if Continues s s' ∧ s'.2 = h ∧ h ∈ disagreeSet s.1 ∧ inExcursion h s = true then 1 else 0 : ℕ) = 32) ∧
    (∀ h j : Fin 5, j ≠ h → ((excursionStates h).filter fun s => s.2 ≠ j ∧ j ∈ disagreeSet s.1).card = 31) ∧
    (∀ h j : Fin 5,
      (Finset.univ.filter fun s : State => (inExcursion h s = true ∨ s = (lastDirectionRel h, h)) ∧ s.2 ≠ j).card = 60) ∧
    (∀ h j : Fin 5, (Finset.univ.filter fun s : State =>
      (inExcursion h s = true ∨ s = (lastDirectionRel h, h)) ∧ s.2 ≠ j ∧ j ∈ disagreeSet s.1).card = 32) ∧
    (∀ (h : Fin 5) (U : Fin 16), U ≠ 0 →
      (Finset.univ.filter fun p : State × State =>
        p.1.1 = U ∧ inExcursion h p.1 = true ∧ Continues p.1 p.2 ∧ p.2.2 = h).card = 4) ∧
    (∀ (h : Fin 5) (U : Fin 16), U ≠ 0 →
      (Finset.univ.filter fun p : State × State =>
        p.1.1 = U ∧ (inExcursion h p.1 = true ∨ p.1 = (lastDirectionRel h, h)) ∧ Continues p.1 p.2 ∧ p.2.2 = h).card = 4) ∧
    (∀ h t : Fin 5, inExcursion h (0, t) = false) ∧
    (Num.El / 5 - 1 / 5 = Num.EH ∧ (Num.El - 1) / 5 = Num.EH ∧ (Num.Ch : ℝ) / 20 = Num.EH) :=
  ⟨arcs_along, GroupsContinuumLaw.transitions_per_relation, availableTransitions_along, count_moved_availableTransitions, Comp.availableTransitions_moved_other,
    record_count, Comp.availableTransitions_moved_record, Comp.availableTransitions_transitions_per_relation, Comp.availableTransitions_record_transitions_per_relation,
    Comp.singlet_outside_availableTransitions,
    ⟨by rw [Num.El_eq, Num.EH_eq]; norm_num, by rw [Num.El_eq, Num.EH_eq]; norm_num,
      by rw [Num.Ch_eq, Num.EH_eq]; norm_num⟩⟩

/-- **Proposition 194 (the coupling derived).** Each step R1 to R6 as its finite statement: the sixteen two-spinor states
are orthonormal and a step of either line at a two-spinor state is one step up to the agreement sign (R1); a unit moved rotation
has mass `2`, the line's clock is moved at `{r}`, the meeting's division moves `(n r)` exactly at the `8` two-spinor states
containing `r` (R2); `{r, n}` moves `8`, keeps `7`, and the two pairings are the line side and the meeting side (R3);
the bound state's transitions are the `60` steps along `r` off the singlet, `4` at each two-spinor state (R4); the share is
`𝟏ᵀB_rΛ_rΠ𝟏/𝟏ᵀB_rΠ𝟏 = 32/60` (R5), the same along `h` in the available transitions of `h` and along every line (R6):
`c = 8/15`, `1 − c = 7/15`.

Recognition (C): that the cross spread of the bound state is this count of transitions at which its clocks are one rotation is the
theory's identification of the coupling (R5's inference); Lean proves the count. -/
theorem prop_194 :
    ((∀ (u : Fin 5) (k : Fin 16),
      (γ u ⊗ₖ γ u) *ᵥ rel k = (if u ∈ disagreeSet k then -1 else 1 : ℂ) • rel k) ∧
      (∀ (u : Fin 5) (k : Fin 16), count u *ᵥ rel k = (if u ∈ disagreeSet k then 1 else 0 : ℂ) • rel k) ∧
      (∀ k l : Fin 16, star (rel k) ⬝ᵥ rel l = if k = l then 1 else 0)) ∧
    (∀ r : Fin 5, ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1)) = 32 / 60) ∧
    (∀ h : Fin 5, ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * lamR h * availableTransitionsProj h) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * availableTransitionsProj h) *ᵥ 1)) = 8 / 15) ∧
    ((32 : ℚ) / 60 = 8 / 15 ∧ 1 - (8 : ℚ) / 15 = 7 / 15) :=
  ⟨GroupsContinuumLaw.coupling_R1, fun r => (GroupsContinuumLaw.coupling_R5 r).1, GroupsContinuumLaw.coupling_R6.1, GroupsContinuumLaw.coupling_derived⟩

/-- **Proposition 195 (the operator that carries the coupling).** On the eighty states
`c = 𝟏ᵀB_rΛ_rΠ𝟏/𝟏ᵀB_rΠ𝟏 = 32/60 = 8/15` for every line `r`, and with `Π` the available transitions of `h`, along `h`, the same `8/15`;
the meeting matrix is a trace over the records, `Σ_{S≠∅}(4/60)G(S)∘G(S) = I + (8/15)(𝟏𝟏ᵀ − I)`; the composite
operator of the two eigen-levels at `G₁₂ = (8/15)^{1/2}` carries the cross term `−(8/15)(12/125)S₁S₂` at second
order. -/
theorem prop_195 :
    (∀ r : Fin 5, (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1) = 32 ∧
      (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1) = 60 ∧
      ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1)) = 8 / 15) ∧
    (∀ h : Fin 5, ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * lamR h * availableTransitionsProj h) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * availableTransitionsProj h) *ᵥ 1)) = 8 / 15) ∧
    (∀ r : Fin 5,
      ∑ U ∈ Finset.univ.filter (fun U : Fin 16 => U ≠ 0), (4 / 60 : ℚ) • (recordG r U ⊙ recordG r U) =
        1 + (8 / 15 : ℚ) • ((Matrix.of fun _ _ => (1 : ℚ)) - 1)) ∧
    (∀ S₁ S₂ : ℝ, 0 ≤ (S₁ - S₂) ^ 2 + 4 * (8 / 15) * S₁ * S₂ →
      (eigenPlus S₁ S₂ (8 / 15) / 5 - 6 / 125 * eigenPlus S₁ S₂ (8 / 15) ^ 2) +
          (eigenMinus S₁ S₂ (8 / 15) / 5 - 6 / 125 * eigenMinus S₁ S₂ (8 / 15) ^ 2) =
        (S₁ + S₂) / 5 - 6 / 125 * (S₁ ^ 2 + S₂ ^ 2) - (8 / 15) * (12 / 125) * S₁ * S₂) := by
  refine ⟨prop195, prop195_availableTransitions, meeting_matrix_trace, fun S₁ S₂ hd => ?_⟩
  rw [second_order_composite S₁ S₂ (8 / 15) hd]
  ring

/-- **Proposition 197 (the light level, from the charged pion through the composition).**
`6m_p²Tr δ₁(R(R_udS_d, S_d; 8/15)) = m_π⁰²` has exactly one nonnegative root `S_d`, in `[sdLo, sdHi]` (relative width
`2·10⁻¹⁷`): `S_d = 0.011855816`, `S_u = R_udS_d = 0.005447267` (`R_ud = 17/37`), `S_s = pS_d = 0.236661685`.

The digits of `S_u` and `S_s` are `Comp.light_level_digits` (`Remainders.lean`); the whole proposition is `prop_197`
(`Whole.lean`). -/
theorem Completion.Comp.light_level :
    (∃ S ∈ Set.Icc Article.sdLo Article.sdHi, light_level_equation S Num.mp (Table.Row.G06 ^ 2)) ∧
    (∀ S T : ℝ, 0 ≤ S → 0 ≤ T → light_level_equation S Num.mp (Table.Row.G06 ^ 2) →
      light_level_equation T Num.mp (Table.Row.G06 ^ 2) → S = T) ∧
    (∀ S : ℝ, 0 ≤ S → light_level_equation S Num.mp (Table.Row.G06 ^ 2) → Article.Bnd S Article.sdLo Article.sdHi) ∧
    ((0.0118558155 : ℝ) < Article.sdLo ∧ Article.sdHi < 0.0118558165) := by
  rw [Num.mp_eq_q, Table.G06_eq_q]
  refine ⟨Article.light_level_exists, Article.light_level_unique, Article.light_level_mem, ?_⟩
  rw [Article.sdLo, Article.sdHi]
  norm_num

/-- **Equation (48), the level operator.** As Prop. 189 with `R = D^{1/2}GD^{1/2}`, `δ = Tr δ₁(R)`,
`δ₁(S) = −log((3 + (9 + 16e^{−S})^{1/2})/8)`; the triangle of three lines with phases has
`det G₃ = 1 − 3c + 2c^{3/2}cos φ` (`c = g²`), and positivity at `c = 8/15` keeps only the flat triangle among the
quarter-turn phases. -/
theorem eq_48 :
    (∀ S : ℝ, deltaLevel S = -Real.log ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : Gᵀ = G) (S : ι → ℝ), (∀ i, 0 < S i) →
      ∀ {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ),
        (1 - (G * diagonal S) ⊗ₖ X).det = ∏ j, (1 - (Comp.levelR_herm hG S).eigenvalues j • X).det) ∧
    (∀ g a b d : ℝ,
      (!![(1 : ℂ), g * Complex.exp (a * Complex.I), g * Complex.exp (d * Complex.I);
          g * Complex.exp (-(a : ℂ) * Complex.I), 1, g * Complex.exp (b * Complex.I);
          g * Complex.exp (-(d : ℂ) * Complex.I), g * Complex.exp (-(b : ℂ) * Complex.I), 1]).det =
        ((1 - 3 * g ^ 2 + 2 * g ^ 3 * Real.cos (a + b - d) : ℝ) : ℂ)) ∧
    ((0 : ℝ) < 1 - 3 * (8 / 15) + 2 * (8 / 15) * √(8 / 15) * Real.cos 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos (π / 2) < 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos π < 0 ∧
      1 - 3 * (8 / 15 : ℝ) + 2 * (8 / 15) * √(8 / 15) * Real.cos (3 * π / 2) < 0) :=
  ⟨level_value, fun {ι} _ _ G hG S hS {n} _ _ X => Comp.modes_det hG hS X, Comp.det_triangle,
    Comp.quarter_turn_positivity⟩

/-- **Equation (49), equal coupling.** For `n + 1` equal lines `δ = n δ₁((1 − g)S) + δ₁((1 + ng)S)`, `g = c^{1/2}`;
a positive level saturates at `log(4/3)`, and both roots `r_± = (3 ± (9 + 16e^{−S})^{1/2})/8` solve
`4r² − 3r − e^{−S} = 0`. -/
theorem eq_49 :
    (∀ (n : ℕ) (S g : ℝ) (f : ℝ → ℝ),
      Article.trF f (S • Article.eqG n g) = n * f ((1 - g) * S) + f ((1 + n * g) * S)) ∧
    (∀ S : ℝ, deltaLevel S < Real.log (4 / 3)) ∧ Tendsto deltaLevel atTop (𝓝 (Real.log (4 / 3))) ∧
    (∀ S : ℝ, 4 * ((3 + √(9 + 16 * Real.exp (-S))) / 8) ^ 2 - 3 * ((3 + √(9 + 16 * Real.exp (-S))) / 8) -
          Real.exp (-S) = 0 ∧
        4 * ((3 - √(9 + 16 * Real.exp (-S))) / 8) ^ 2 - 3 * ((3 - √(9 + 16 * Real.exp (-S))) / 8) -
          Real.exp (-S) = 0 ∧
        deltaLevel S = -Real.log ((3 + √(9 + 16 * Real.exp (-S))) / 8)) :=
  ⟨Article.equal_coupling_trace, Comp.level_saturation.1, Comp.level_saturation.2.1, Comp.level_saturation.2.2⟩

/-- **Equation (50), the incidence polynomial.** `B = B_d[C(A,2) + (13/16)C(A,3) + (61/16)C(A,4)] − (αm_p/9)C(Z,2)`,
with `13/16 = χ_AVar Q/Eℓ`, `61/16 = k_C + 13/16 = Var D` and `9 = Var P − Cov²/Var Q`, law-tied: the triton, the
helion and helium-4 (rows N01, N02, N03). -/
theorem eq_50 :
    Table.Row.tau3 = 13 / 16 ∧ (Num.kC : ℝ) + Table.Row.tau3 = 61 / 16 ∧ Table.Row.VC = 9 ∧
    Table.Row.N01 = Table.Row.Binc 3 1 ∧ Table.Row.N02 = Table.Row.Binc 3 2 ∧ Table.Row.N03 = Table.Row.Binc 4 2 ∧
    ((8.481159640565 : ℝ) < Table.Row.N01 ∧ Table.Row.N01 < 8.481159640575) ∧
    ((7.720392725255 : ℝ) < Table.Row.N02 ∧ Table.Row.N02 < 7.720392725265) ∧
    ((28.29763250885 : ℝ) < Table.Row.N03 ∧ Table.Row.N03 < 28.29763250895) := by
  refine ⟨Table.tau3_eq, ?_, Table.VC_eq, rfl, rfl, rfl, row_N01, row_N02, row_N03⟩
  rw [Table.tau3_eq, Num.kC_eq]
  norm_num

/-- **Proposition 196 (the seven retained rows are unchanged).** Law-tied:
`m_p/m_e = 6M + C_h + (1/6)log(5/2) − a⁵ − ba⁶`, `m_n/m_p = (5/2)^{5a⁴ + 4a¹⁰ + 10c_Lba⁶}`, `m_Λ = m_n(5/2)^{60/320}`,
`m_Δ = 3bm_p = (21/16)m_p`, `m_π⁰² = 38hm_em_p`, `m_π±² = m_π⁰² + Δ_el` with `Δ_el = παm_p²/(Eℓ(1 − αbΦ(i)))`,
`Re s_ρ = 6m_p²log x_c`; against the records (CODATA 2022 `1836.152673426(32)`, `1.00137841946(40)`; PDG
`1115.683(6)`, `1232(2)`, `134.9768(5)`, `139.57039(18)` MeV; `0.577879(2449)` GeV², outside inputs) they stand at
`−0.44, +0.26, −0.02, −0.26, +0.49, −0.02, −0.60` standard deviations. -/
theorem prop_196 :
    Table.Row.B12 = 6 * (Num.M : ℝ) + Num.Ch + Real.log Num.EU / Num.LOmega - Num.a ^ 5 - Num.b * Num.a ^ 6 ∧
    Table.Row.B13 = Num.EU ^ (5 * Num.a ^ 4 + 4 * Num.a ^ 10 + 10 * Num.cL * Num.b * Num.a ^ 6) ∧
    Table.Row.J03 = Table.Row.mn * (5 / 2) ^ (3 / 16 : ℝ) ∧ (3 / 16 : ℝ) = (Num.Ch : ℝ) / (arcs.card : ℝ) ∧
    Table.Row.G02 = 3 * Num.b * Num.mp ∧ Table.Row.G06 = √(38 * Num.h * Num.me * Num.mp) ∧
    Table.Row.G07 = √(Table.Row.G06 ^ 2 + Table.Row.Del) ∧
    Table.Row.J07 = 6 * Num.mp ^ 2 * Real.log ((√313 - 11) / 6) / 1000000 ∧
    ((-0.445 : ℝ) < (Table.Row.B12 - 1836.152673426) / 3.2e-8 ∧ (Table.Row.B12 - 1836.152673426) / 3.2e-8 < -0.435) ∧
    ((0.255 : ℝ) < (Table.Row.B13 - 1.00137841946) / 4e-10 ∧ (Table.Row.B13 - 1.00137841946) / 4e-10 < 0.265) ∧
    ((-0.025 : ℝ) < (Table.Row.J03 - 1115.683) / 0.006 ∧ (Table.Row.J03 - 1115.683) / 0.006 < -0.015) ∧
    ((-0.265 : ℝ) < (Table.Row.G02 - 1232) / 2 ∧ (Table.Row.G02 - 1232) / 2 < -0.255) ∧
    ((0.485 : ℝ) < (Table.Row.G06 - 134.9768) / 0.0005 ∧ (Table.Row.G06 - 134.9768) / 0.0005 < 0.495) ∧
    ((-0.025 : ℝ) < (Table.Row.G07 - 139.57039) / 0.00018 ∧ (Table.Row.G07 - 139.57039) / 0.00018 < -0.015) ∧
    ((-0.605 : ℝ) < (Table.Row.J07 - 0.577879) / 0.002449 ∧ (Table.Row.J07 - 0.577879) / 0.002449 < -0.595) := by
  have b12 : Article.Bnd Table.Row.B12 (1.8361526734120517861459969e3 : ℝ) (1.8361526734120517861459972e3 : ℝ) := by
    rw [Table.B12_eq_q]; exact Article.rowB12_bnd
  have b13 : Article.Bnd Table.Row.B13 (1.0013784195646195665100965 : ℝ) (1.0013784195646195665100966 : ℝ) := by
    rw [Table.B13_eq_q]; exact Article.rowB13_bnd
  have j03 : Article.Bnd Table.Row.J03 (1.1156829009076869889335957e3 : ℝ) (1.1156829009076869889335962e3 : ℝ) := by
    rw [(row_J03).1, Table.mn_eq_q]; exact Article.rowJ03_bnd
  have g02 : Article.Bnd Table.Row.G02 (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := by
    rw [(row_G02).1, Num.mp_eq_q]; exact Article.rowG02_bnd
  have g06 : Article.Bnd Table.Row.G06 (1.349770445597686281871865e2 : ℝ) (1.3497704455976862818718656e2 : ℝ) := by
    rw [Table.G06_eq_q]; exact Article.rowG06_bnd
  have g07 : Article.Bnd Table.Row.G07 (1.3957038661380855965663077e2 : ℝ) (1.3957038661380855965664527e2 : ℝ) := by
    rw [Table.G07_eq_q]; exact Article.rowG07_bnd
  have j07 : Article.Bnd Table.Row.J07 (5.7640855549429342808959105e-1 : ℝ) (5.7640855549429342808959655e-1 : ℝ) := by
    rw [(row_J07).1, Num.mp_eq_q]; exact Article.rowJ07_bnd
  refine ⟨by rw [(row_B12).1, Num.M_eq, Num.Ch_eq, Num.EU_eq, Num.LOmega_eq, Num.a_eq, Num.b_eq]; push_cast; ring,
    by rw [(row_B13).1, Num.EU_eq, Num.a_eq, Num.cL_eq, Num.b_eq], (row_J03).1,
    by rw [Num.Ch_eq, Comparison.card_arcs]; norm_num, by rw [Table.Row.G02, Num.kC_eq]; push_cast; ring,
    (row_G06).1, (row_G07).1, (row_J07).1,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith [b12.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [b12.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [b13.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [b13.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [j03.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [j03.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [g02.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [g02.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [g06.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [g06.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [g07.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [g07.2]
  · rw [lt_div_iff₀ (by norm_num)]; linarith [j07.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [j07.2]

/-- **Proposition 198 (`K⁰`).** `K⁰ = d s̄` at the singlet: `m² = 6m_p²Tr δ₁(R(S_d, S_s; 8/15))` with the light level
`S_d` (Prop. 197) and `S_s = pS_d`, `p = m_s/m_d` the plane-and-singlet mass operator; the law on the direct sum factors over
the two modes; at `c = 0` the composition is the line side `δ₁(S_d) + δ₁(S_s)` and at `c = 1` the meeting side
`δ₁(S_d + S_s)`; `m = 497.6135845 MeV`, against `497.611(13)` (PDG, outside input), `+0.20` standard deviations.

The refits at every coupling (the line side alone, the meeting side alone, the asks in `c` and `p`, the shift's
form) are `Comp.kaon_every_coupling` (`Kaon.lean`); the whole proposition is `prop_198` (`Whole.lean`). -/
theorem Completion.Comp.kaon_book :
    Table.Row.J08 = Article.rowJ08Of Table.Row.Sd ∧ light_level_equation Table.Row.Sd Num.mp (Table.Row.G06 ^ 2) ∧
    Article.rowJ08Of Table.Row.Sd =
      Num.mp * √(6 * (deltaLevel (Table.Row.Sd * Article.qNuP) + deltaLevel (Table.Row.Sd * Article.qNuM))) ∧
    (6 * Num.mp ^ 2 * compositeDelta Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) 0 =
        6 * Num.mp ^ 2 * (deltaLevel Table.Row.Sd + deltaLevel (massOp .symmetric sPlaneSinglet * Table.Row.Sd)) ∧
      6 * Num.mp ^ 2 * compositeDelta Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) 1 =
        6 * Num.mp ^ 2 * deltaLevel (Table.Row.Sd + massOp .symmetric sPlaneSinglet * Table.Row.Sd) ∧
      eigenPlus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) +
          eigenMinus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) =
        Table.Row.Sd + massOp .symmetric sPlaneSinglet * Table.Row.Sd ∧
      massOp .symmetric sPlaneSinglet =
        3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * clockMQ sLastDirectionSinglet (-(9 / 4000)) ^ (1 / 6 : ℝ)) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ), 0 < Table.Row.Sd →
      (1 - levelOp Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (Real.sqrt (8 / 15)) ⊗ₖ M).det =
        (1 - eigenPlus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) • M).det *
          (1 - eigenMinus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) • M).det) ∧
    ((497.6135844505 : ℝ) < Table.Row.J08 ∧ Table.Row.J08 < 497.6135844515) ∧
    ((0.195 : ℝ) < (Table.Row.J08 - 497.611) / 0.013 ∧ (Table.Row.J08 - 497.611) / 0.013 < 0.205) := by
  rw [Num.mp_eq_q, Table.G06_eq_q]
  have hJ := row_J08
  refine ⟨rfl, Table.Sd_eq, Article.rowJ08Of_eq _ Table.Sd_nonneg,
    K0_composition _ _ Table.Sd_nonneg (massOp_plane_pos _).le, fun M hS => K0_law_on_direct_sum _ hS M, hJ,
    ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith [hJ.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [hJ.2]

end Comparison.System
