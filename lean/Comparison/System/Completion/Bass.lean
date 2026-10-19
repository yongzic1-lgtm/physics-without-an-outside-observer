import Comparison.System.Completion.Pairings

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 12: Bass's identity with a weight on each step (SI Prop. 161, complete)

`Law.ihara_bass_weighted` holds for five operators with scalar squares; here the squares are
any matrices `D_t = Γ_t²` (`ihara_bass_diag`, the same proof with `E = blockDiagonal(1 − u²D_t)`). A weight on each
step together with any connection is a matrix `W e` on an internal space `n` for each step `e` (the step from `k` to
`transition t k` carries `W t (transition t k) k`); then `Γ_t² = blockDiagonal(W_eW_ē)` (`stepMat_sq`) and
`det(1 − uΓ_t) = Π_{links of t} det(1 − u²W_eW_ē)` (`det_stepMat`), by the sign `S_t` that changes at each link
(`S_tΓ_tS_t = −Γ_t`), `det(1 − cAB) = det(1 − cBA)`, and the polynomial identity `F² = G²`, `F(0) = G(0) = 1`.
-/

namespace Comparison.System.Completion.Comp

open Matrix Polynomial Comparison Comparison.Law

section Diag

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- **Bass's identity for five operators with any squares** `Γ_t² = D_t`. -/
theorem ihara_bass_diag (Γ D : Fin 5 → Matrix V V K) (hΓ : ∀ t, Γ t * Γ t = D t) (u : K)
    (hD : ∀ t, IsUnit (1 - u ^ 2 • D t).det) :
    (∏ t, (1 - u • Γ t).det) * (1 - u • stepOp Γ).det =
      (∏ t, (1 - u ^ 2 • D t).det) * (1 - ∑ t, (1 - u ^ 2 • D t)⁻¹ * (u • (Γ t - u • D t))).det := by
  set bd := blockDiagonal Γ with hbd
  have hbd2 : bd * bd = blockDiagonal D := by
    rw [hbd, ← blockDiagonal_mul]
    simp only [hΓ]
  have hdetG : (1 - u • bd).det = ∏ t, (1 - u • Γ t).det := by
    have h : (blockDiagonal fun t => 1 - u • Γ t) = 1 - u • bd := by
      rw [hbd, show (fun t => 1 - u • Γ t) = (1 : Fin 5 → Matrix V V K) - u • Γ from rfl,
        blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
    rw [← h, det_blockDiagonal]
  set E : Matrix (V × Fin 5) (V × Fin 5) K := blockDiagonal fun t => 1 - u ^ 2 • D t with hE
  set Einv : Matrix (V × Fin 5) (V × Fin 5) K := blockDiagonal fun t => (1 - u ^ 2 • D t)⁻¹ with hEinv
  have hEEinv : E * Einv = 1 := by
    rw [hE, hEinv, ← blockDiagonal_mul]
    have : (fun t => (1 - u ^ 2 • D t) * (1 - u ^ 2 • D t)⁻¹) = fun _ => (1 : Matrix V V K) := by
      funext t
      exact Matrix.mul_nonsing_inv _ (hD t)
    rw [this]
    exact blockDiagonal_one
  have hEeq : E = 1 - u ^ 2 • (bd * bd) := by
    rw [hbd2, hE, show (fun t => 1 - u ^ 2 • D t) = (1 : Fin 5 → Matrix V V K) - u ^ 2 • D from rfl,
      blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
  have hdetE : E.det = ∏ t, (1 - u ^ 2 • D t).det := by
    rw [hE, det_blockDiagonal]
  have hprod : (1 - u • bd) * (1 - u • stepOp Γ) =
      E * (1 - (Einv * (u • (bd - u • (bd * bd))) * colX V K) * rowY V K) := by
    have hL : (1 - u • bd) * (1 - u • stepOp Γ) =
        E - (u • (bd - u • (bd * bd)) * colX V K) * rowY V K := by
      rw [stepOp_eq, hEeq]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_assoc, smul_sub, smul_smul]
      rw [← hbd]
      simp only [← Matrix.mul_assoc]
      module
    rw [hL]
    have e : E * (1 - Einv * (u • (bd - u • (bd * bd))) * colX V K * rowY V K) =
        E - (E * Einv) * (u • (bd - u • (bd * bd))) * colX V K * rowY V K := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [e, hEEinv, Matrix.one_mul]
  have hcollapse : rowY V K * (Einv * (u • (bd - u • (bd * bd))) * colX V K) =
      ∑ t, (1 - u ^ 2 • D t)⁻¹ * (u • (Γ t - u • D t)) := by
    have hblk : Einv * (u • (bd - u • (bd * bd))) =
        blockDiagonal fun t => (1 - u ^ 2 • D t)⁻¹ * (u • (Γ t - u • D t)) := by
      rw [hbd2, hEinv, hbd, ← blockDiagonal_smul, ← blockDiagonal_sub, ← blockDiagonal_smul,
        ← blockDiagonal_mul]
      rfl
    rw [hblk, ← Matrix.mul_assoc, rowY_blockDiagonal_colX]
  have h := congrArg Matrix.det hprod
  rw [det_mul, det_mul, hdetG, det_one_sub_mul_comm, hcollapse, hdetE] at h
  exact h

end Diag

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The sign that changes at each link along `t`. -/
def linkSign (t : Fin 5) (k : Fin 16) : K := if k < transition t k then 1 else -1

theorem linkSign_transition (t : Fin 5) (k : Fin 16) :
    linkSign (K := K) t (transition t k) * linkSign (K := K) t k = -1 := by
  unfold linkSign
  rcases lt_or_gt_of_ne (transition_ne t k) with h1 | h1
  · have hk : ¬ k < transition t k := not_lt.mpr h1.le
    simp [transition_transition, hk, h1]
  · have hk2 : ¬ transition t k < k := not_lt.mpr h1.le
    simp [transition_transition, h1, hk2]

theorem linkSign_sq (t : Fin 5) (k : Fin 16) : linkSign (K := K) t k * linkSign (K := K) t k = 1 := by
  unfold linkSign
  split_ifs <;> norm_num

/-- The lower end of each link along `t`. -/
def lowEnds (t : Fin 5) : Finset (Fin 16) := Finset.univ.filter fun k => k < transition t k

/-- **`Π_k f(k)` over the sixteen vertices is the square of the product over the eight links.** -/
theorem prod_places_links {R : Type*} [CommMonoid R] (f : Fin 16 → R) (t : Fin 5) (hf : ∀ k, f (transition t k) = f k) :
    ∏ k, f k = (∏ k ∈ lowEnds t, f k) * (∏ k ∈ lowEnds t, f k) := by
  unfold lowEnds
  have hU : ∏ k ∈ Finset.univ.filter (fun k => ¬ k < transition t k), f k =
      ∏ k ∈ Finset.univ.filter (fun k => k < transition t k), f k := by
    refine Finset.prod_nbij' (fun k => transition t k) (fun k => transition t k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [transition_transition]
      rcases lt_or_gt_of_ne (transition_ne t k) with h1 | h1
      · exact h1
      · exact absurd h1 hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [transition_transition]
      exact not_lt.mpr hk.le
    · intro k _
      exact transition_transition t k
    · intro k _
      exact transition_transition t k
    · intro k _
      exact (hf k).symm
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => k < transition t k), hU]

/-- **The step operator along `t` with a matrix on each step** (a weight times a connection on an internal space `n`):
the step from the vertex `k` to `transition t k` carries `W t (transition t k) k`. -/
def stepMat (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) : Matrix (n × Fin 16) (n × Fin 16) K :=
  Matrix.of fun p q => if p.2 = transition t q.2 then W t p.2 q.2 p.1 q.1 else 0

/-- `W_eW_ē` at the vertex `k`, `e` the step along `t` into `k`. -/
def linkMat (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) (k : Fin 16) : Matrix n n K :=
  W t k (transition t k) * W t (transition t k) k

theorem stepMat_sq (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) :
    stepMat W t * stepMat W t = blockDiagonal (linkMat W t) := by
  ext ⟨a, x⟩ ⟨c, z⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply]
  simp only [stepMat, Matrix.of_apply]
  have hy : ∀ b, ∑ y, (if x = transition t y then W t x y a b else 0) * (if y = transition t z then W t y z b c else 0) =
      if x = z then W t x (transition t z) a b * W t (transition t z) z b c else 0 := by
    intro b
    rw [Finset.sum_eq_single (transition t z)]
    · rw [transition_transition]
      by_cases hxz : x = z
      · simp [hxz]
      · simp [hxz]
    · intro y _ hy
      simp [hy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [hy]
  by_cases hxz : x = z
  · subst hxz
    simp [linkMat, Matrix.mul_apply]
  · simp [hxz]

theorem sign_conjM (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) :
    diagonal (fun p : n × Fin 16 => linkSign (K := K) t p.2) * stepMat W t *
      diagonal (fun p : n × Fin 16 => linkSign (K := K) t p.2) = -stepMat W t := by
  ext ⟨a, x⟩ ⟨c, z⟩
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, stepMat, Matrix.of_apply]
  by_cases h : x = transition t z
  · subst h
    rw [ite_eq_left rfl]
    have := linkSign_transition (K := K) t z
    linear_combination W t (transition t z) z a c * this
  · simp [h]

/-- `det(1 − cAB) = det(1 − cBA)`. -/
theorem det_one_sub_smul_mul_comm {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (c : R) (A B : Matrix m m R) : (1 - c • (A * B)).det = (1 - c • (B * A)).det := by
  rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]

theorem linkMat_det_transition (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) (k : Fin 16) (c : K) :
    (1 - c • linkMat W t (transition t k)).det = (1 - c • linkMat W t k).det := by
  rw [linkMat, linkMat, transition_transition, det_one_sub_smul_mul_comm]

/-- Evaluating `1 − p·A` at `u` gives `1 − p(u)A`. -/
theorem evalMap_one_sub_smul {m : Type*} [Fintype m] [DecidableEq m] (p : K[X]) (A : Matrix m m K) (u : K) :
    (Polynomial.evalRingHom u).mapMatrix (1 - p • A.map C) = 1 - p.eval u • A := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Matrix.one_apply]
  split_ifs <;> simp

theorem det_eval_one_sub_smul {m : Type*} [Fintype m] [DecidableEq m] (p : K[X]) (A : Matrix m m K) (u : K) :
    ((1 - p • A.map C).det).eval u = (1 - p.eval u • A).det := by
  rw [← evalMap_one_sub_smul p A u, ← RingHom.map_det, Polynomial.coe_evalRingHom]

/-- A sign `S` with `S² = 1` and `SNS = −N` gives `det(1 + N) = det(1 − N)`. -/
theorem det_one_add_eq_of_sign {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (N S : Matrix m m R) (hS2 : S * S = 1) (hS : S * N * S = -N) : (1 + N).det = (1 - N).det := by
  have e : 1 + N = S * (1 - N) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS2, hS, sub_neg_eq_add]
  have hdS : S.det * S.det = 1 := by rw [← det_mul, hS2, det_one]
  rw [e, det_mul, det_mul]
  linear_combination (1 - N).det * hdS

variable [CharZero K]

/-- Two polynomials with equal squares and the value `1` at `0` are equal. -/
theorem poly_eq_of_sq_eq {F G : K[X]} (h : F * F = G * G) (hF : F.eval 0 = 1) (hG : G.eval 0 = 1) : F = G := by
  rcases mul_self_eq_mul_self_iff.mp h with h1 | h1
  · exact h1
  · exfalso
    have h2 := congrArg (Polynomial.eval 0) h1
    rw [hF, Polynomial.eval_neg, hG] at h2
    norm_num at h2

/-- **`det(1 − uΓ_t) = Π_{links of t} det(1 − u²W_eW_ē)`** for every matrix on the steps along `t`. -/
theorem det_stepMat (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (t : Fin 5) (u : K) :
    (1 - u • stepMat W t).det = ∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (n × Fin 16) (n × Fin 16) K[X], M = (stepMat W t).map C := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S : Matrix (n × Fin 16) (n × Fin 16) K[X],
      S = diagonal (fun p : n × Fin 16 => C (linkSign (K := K) t p.2)) := ⟨_, rfl⟩
  have hsq : M * M = blockDiagonal fun k => (linkMat W t k).map C := by
    rw [hM, ← Matrix.map_mul, stepMat_sq, blockDiagonal_map _ _ (map_zero C)]
  have hS : S * M * S = -M := by
    have h := congrArg (fun A => A.map C) (sign_conjM (K := K) W t)
    simp only [Matrix.map_mul, diagonal_map (map_zero C)] at h
    rw [Matrix.map_neg _ (map_neg C)] at h
    rw [hSd, hM]
    exact h
  have hS2 : S * S = 1 := by
    rw [hSd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext p
    rw [← C_mul, linkSign_sq, C_1]
  have hSX : S * ((X : K[X]) • M) * S = -((X : K[X]) • M) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hS, smul_neg]
  have hplus : (1 + (X : K[X]) • M).det = (1 - (X : K[X]) • M).det :=
    det_one_add_eq_of_sign _ S hS2 hSX
  have hmat : (1 - (X : K[X]) • M) * (1 + (X : K[X]) • M) = 1 - (X : K[X]) ^ 2 • (M * M) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sq]
    abel
  have hblk : (1 : Matrix (n × Fin 16) (n × Fin 16) K[X]) -
        (X : K[X]) ^ 2 • (blockDiagonal fun k => (linkMat W t k).map C) =
      blockDiagonal fun k => 1 - (X : K[X]) ^ 2 • (linkMat W t k).map C := by
    rw [show (fun k => 1 - (X : K[X]) ^ 2 • (linkMat W t k).map C) =
        (1 : Fin 16 → Matrix n n K[X]) - (X : K[X]) ^ 2 • (fun k => (linkMat W t k).map C) from rfl,
      blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
  have hf : ∀ k, (1 - (X : K[X]) ^ 2 • (linkMat W t (transition t k)).map C).det =
      (1 - (X : K[X]) ^ 2 • (linkMat W t k).map C).det := by
    intro k
    rw [linkMat, linkMat, transition_transition, Matrix.map_mul, Matrix.map_mul, det_one_sub_smul_mul_comm]
  have hFF : (1 - (X : K[X]) • M).det * (1 - (X : K[X]) • M).det =
      (∏ k ∈ lowEnds t, (1 - (X : K[X]) ^ 2 • (linkMat W t k).map C).det) *
        (∏ k ∈ lowEnds t, (1 - (X : K[X]) ^ 2 • (linkMat W t k).map C).det) := by
    rw [← prod_places_links (fun k => (1 - (X : K[X]) ^ 2 • (linkMat W t k).map C).det) t hf,
      ← det_blockDiagonal, ← hblk, ← hsq, ← hmat, det_mul, hplus]
  have e1 : ((1 - (X : K[X]) • M).det).eval 0 = 1 := by
    rw [hM, det_eval_one_sub_smul, Polynomial.eval_X, zero_smul, sub_zero, det_one]
  have e2 : (∏ k ∈ lowEnds t, (1 - (X : K[X]) ^ 2 • (linkMat W t k).map C).det).eval 0 = 1 := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [det_eval_one_sub_smul, Polynomial.eval_pow, Polynomial.eval_X, zero_pow two_ne_zero, zero_smul, sub_zero,
      det_one]
  have hFG := poly_eq_of_sq_eq hFF e1 e2
  have hu := det_eval_one_sub_smul (X : K[X]) (stepMat W t) u
  rw [Polynomial.eval_X, ← hM, hFG, Polynomial.eval_prod] at hu
  rw [← hu]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [det_eval_one_sub_smul, Polynomial.eval_pow, Polynomial.eval_X]

end Comparison.System.Completion.Comp

namespace Comparison.System

open Matrix Comparison.Law Comparison.System.Completion.Comp

/-- **SI Prop. 161, the vertex form** (a weight `W_e` on each step and any connection, carried as a matrix on an
internal space `n`): wherever every `det(1 − u²W_eW_ē) ≠ 0`, on the sixteen vertices,
`det(I − uB_W) = Π_links det(1 − u²W_eW_ē) · det(I − Â + D̂)` with `Â_xy = u(1 − u²W_eW_ē)⁻¹W_e` for the step `e`
from `y` to `x` and `D̂_xx = Σ_{e into x} u²(1 − u²W_eW_ē)⁻¹W_eW_ē`. -/
theorem Completion.Comp.place_form_steps {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]
    (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n K) (u : K) (hc : ∀ t k, (1 - u ^ 2 • linkMat W t k).det ≠ 0) :
    (1 - u • stepOp (stepMat W)).det =
      (∏ t, ∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det) *
        (1 - ∑ t, u • (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * stepMat W t +
          ∑ t, u ^ 2 • blockDiagonal (fun k => (1 - u ^ 2 • linkMat W t k)⁻¹ * linkMat W t k)).det := by
  set D : Fin 5 → Matrix (n × Fin 16) (n × Fin 16) K := fun t => blockDiagonal (linkMat W t) with hD
  have hΓ : ∀ t, stepMat W t * stepMat W t = D t := fun t => stepMat_sq W t
  have hblk : ∀ t, (1 : Matrix (n × Fin 16) (n × Fin 16) K) - u ^ 2 • D t =
      blockDiagonal fun k => 1 - u ^ 2 • linkMat W t k := by
    intro t
    rw [hD]
    dsimp only
    rw [show (fun k => 1 - u ^ 2 • linkMat W t k) = (1 : Fin 16 → Matrix n n K) - u ^ 2 • linkMat W t from rfl,
      blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
  have hdetD : ∀ t, ((1 : Matrix (n × Fin 16) (n × Fin 16) K) - u ^ 2 • D t).det =
      ∏ k, (1 - u ^ 2 • linkMat W t k).det := by
    intro t
    rw [hblk, det_blockDiagonal]
  have hunit : ∀ t, IsUnit ((1 : Matrix (n × Fin 16) (n × Fin 16) K) - u ^ 2 • D t).det := by
    intro t
    rw [hdetD]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc t k)
  have h := ihara_bass_diag (stepMat W) D hΓ u hunit
  have hG : ∀ t, (1 - u • stepMat W t).det = ∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det :=
    fun t => det_stepMat W t u
  have hinv : ∀ t, ((1 : Matrix (n × Fin 16) (n × Fin 16) K) - u ^ 2 • D t)⁻¹ =
      blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹ := by
    intro t
    rw [hblk]
    apply Matrix.inv_eq_right_inv
    rw [← blockDiagonal_mul]
    rw [show (fun k => (1 - u ^ 2 • linkMat W t k) * (1 - u ^ 2 • linkMat W t k)⁻¹) = fun _ => (1 : Matrix n n K) from
      funext fun k => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hc t k))]
    exact blockDiagonal_one
  have hsq_prod : ∀ t, ∏ k, (1 - u ^ 2 • linkMat W t k).det =
      (∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det) * (∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det) :=
    fun t => prod_places_links _ t (fun k => linkMat_det_transition W t k (u ^ 2))
  have hterm : ∀ t, (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * (u • (stepMat W t - u • D t)) =
      u • (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * stepMat W t -
        u ^ 2 • blockDiagonal (fun k => (1 - u ^ 2 • linkMat W t k)⁻¹ * linkMat W t k) := by
    intro t
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, hD]
    dsimp only
    rw [← blockDiagonal_mul, smul_sub, smul_smul, Matrix.smul_mul, sq]
  have hmat : (1 - ∑ t, (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * (u • (stepMat W t - u • D t))) =
      1 - ∑ t, u • (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * stepMat W t +
        ∑ t, u ^ 2 • blockDiagonal (fun k => (1 - u ^ 2 • linkMat W t k)⁻¹ * linkMat W t k) := by
    rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_sub_distrib]
    abel
  simp only [hG, hdetD, hsq_prod, hinv] at h
  rw [Finset.prod_mul_distrib, hmat] at h
  have hPne : (∏ t, ∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun t _ => Finset.prod_ne_zero_iff.mpr fun k _ => hc t k
  exact mul_left_cancel₀ hPne (by linear_combination h)

open Real Complex Kronecker Comparison Comparison.System.Completion Comparison.Article in
/-- **Proposition 161 (one line, one operator).** Every clause of `Comp.one_line_one_operator` (the secular root and the
Perron root of the line-weighted walk, the singlet meeting's factor, the spectrum under `𝒳 ⊗ 1`, the vertex form with line
weights, the level factor, its root and `u_c(0.3) = 0.264322355220`), and the vertex form with a weight `W_e` on each step
and any connection: for every internal space `n` and every matrix `W_e` on each step,
`det(I − uB_W) = Π_links det(1 − u²W_eW_ē) · det(I − Â + D̂)` on the sixteen vertices, `Â_xy = u(1 − u²W_eW_ē)⁻¹W_e`
for the step `e` from `y` to `x`, `D̂_xx = Σ_{e into x} u²(1 − u²W_eW_ē)⁻¹W_eW_ē`, wherever each
`det(1 − u²W_eW_ē) ≠ 0`. -/
theorem prop_161 :
    ((∀ (w : Fin 5 → ℝ), (∀ t, 0 < w t) → ∀ lam : ℝ, 0 < lam → ∑ t, w t / (lam + w t) = 1 →
       IsPerron (lineWalk w) (lam / 4) ∧ ∑ t, 1 / (1 + (1 / lam) * w t) - 4 = 0) ∧
     (∀ (u : ℝ) (w : Fin 5 → ℝ), (∀ t, 1 + u * w t ≠ 0) →
       (1 - u • (diagonal w * (Matrix.of fun i j : Fin 5 => if i = j then (0 : ℝ) else 1))).det =
         (∏ t, (1 + u * w t)) * (∑ t, 1 / (1 + u * w t) - 4)) ∧
     (∀ (K : Type) [Field K] [CharZero K] (M : Matrix State State K) (l : K),
       (l • (1 : Matrix State State K) - charX80 K * M * charX80 K).det = (l • (1 : Matrix State State K) - M).det) ∧
     (∀ (w : Fin 5 → ℂ) (u : ℂ), (∀ t, 1 - u ^ 2 * w t ^ 2 ≠ 0) →
       (1 - u • stepOp (fun t => w t • transitionMat t)).det =
         (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) *
           (1 - ∑ t, (u / (1 - u ^ 2 * w t ^ 2) * w t) • transitionMat t +
             (∑ t, u ^ 2 / (1 - u ^ 2 * w t ^ 2) * w t ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ)).det) ∧
     (∀ (h : Fin 5) (S u : ℝ), 1 + u ≠ 0 → 1 + u * Real.exp (-S) ≠ 0 →
       ∑ t, 1 / (1 + u * levelW h S t) - 4 = (1 - 3 * u - 4 * u ^ 2 * Real.exp (-S)) / ((1 + u) * (1 + u * Real.exp (-S)))) ∧
     (∀ S : ℝ, 1 - 3 * uLevel S - 4 * uLevel S ^ 2 * Real.exp (-S) = 0) ∧
     (∀ (h : Fin 5) (S : ℝ), IsPerron (lastDirectionWalk h (-S)) (lamLevel S / 4)) ∧
     ((0.2643223552195 : ℝ) < uLevel (3 / 10) ∧ uLevel (3 / 10) < 0.2643223552205)) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (W : Fin 5 → Fin 16 → Fin 16 → Matrix n n ℂ) (u : ℂ),
      (∀ t k, (1 - u ^ 2 • linkMat W t k).det ≠ 0) →
      (1 - u • stepOp (stepMat W)).det =
        (∏ t, ∏ k ∈ lowEnds t, (1 - u ^ 2 • linkMat W t k).det) *
          (1 - ∑ t, u • (blockDiagonal fun k => (1 - u ^ 2 • linkMat W t k)⁻¹) * stepMat W t +
            ∑ t, u ^ 2 • blockDiagonal (fun k => (1 - u ^ 2 • linkMat W t k)⁻¹ * linkMat W t k)).det) :=
  ⟨Completion.Comp.one_line_one_operator, fun _ _ _ W u hc => Completion.Comp.place_form_steps W u hc⟩

end Comparison.System
