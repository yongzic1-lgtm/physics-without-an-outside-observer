import Comparison.System.Postulates
import Comparison.Existence.LogDet
import Comparison.GroupsContinuumLaw.Euler
import Comparison.WholePicture.Connection

/-!
# The proof system, the law: Proposition 52 and equation (12), every closed walk counted once

Jacobi's formula and the logarithm of a determinant as formal
power series (`Existence/LogDet.lean`), the words, their periods and the holonomy of the blocks
(`GroupsContinuumLaw/Euler.lean`), the step with a connection `Bconn c` (`System/Basic.lean`). Here:

* `logZ M = Σ_{r ≥ 1} uʳ Tr Mʳ/r`; `log_Z`: **`Z = det(I − uM)⁻¹` has `Z(0) = 1` and `Z′ = Z·(log Z)′`, and it is
  the only power series with these two properties**: `log Z = Σ_r uʳ Tr Mʳ/r` as formal power series;
* `Bconn_apply`: **`B[U](S′, s; S, t) = [s ≠ t][S′ = S △ T_s] U_{S′S}`**;
* `IsClosedHistory`, `hol_BconnS`, `trace_Bconn_pow`: **`Tr B[U]^r` is the sum over the closed walks of length
  `r` (with a marked first step) of the trace of their holonomy**, every other word of states having holonomy `0`;
* `euler_Bconn`: **`Tr B[U]^r/r = Σ_{d ∣ r} Σ_{ℓ primitive, |ℓ| = d} (1/d)·Tr(hol ℓ)^{r/d}/(r/d)`**, the coefficient
  of `uʳ` of `−Σ_{[ℓ]} log det(1 − u^{|ℓ|} hol ℓ)`, each primitive class counted once;
* `B_mulVec_one`, `quarter_iff`, `quarter_walk`: **each state has four continuations, `(uB)𝟏 = 𝟏 ⟺ u = 1/4`, and
  `B/4` is a walk** (nonnegative entries, rows of sum one);
* `eq_12`, `prop_52`.
-/

open Matrix Comparison Comparison.GroupsContinuumLaw.Euler

namespace Comparison.System

namespace Law

/-! ## The logarithm of the law as a formal power series -/

section LogZ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`log Z = Σ_{r ≥ 1} uʳ Tr Mʳ/r`** as a formal power series. -/
noncomputable def logZ (M : Matrix ι ι ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun r => if r = 0 then 0 else (M ^ r).trace / r

theorem logZ_eq_neg (M : Matrix ι ι ℂ) : logZ M = -logSeries M := by
  ext r
  simp only [logZ, logSeries, PowerSeries.coeff_mk, map_neg]
  split_ifs <;> ring

/-- `det(I − uM)` as a formal power series (a polynomial). -/
noncomputable def detSeries (M : Matrix ι ι ℂ) : PowerSeries ℂ :=
  ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det : PowerSeries ℂ)

/-- **`Z = det(I − uM)⁻¹` and `log Z = Σ_{r ≥ 1} uʳ Tr Mʳ/r`:** `Z·det(I − uM) = 1`, `Z(0) = 1`, `(log Z)(0) = 0`,
`Z′ = Z·(log Z)′`, and every power series `Q` with `Q(0) = 1` and `Q′ = Q·(log Z)′` is `Z`. -/
theorem log_Z (M : Matrix ι ι ℂ) :
    (detSeries M)⁻¹ * detSeries M = 1 ∧
    PowerSeries.constantCoeff (detSeries M)⁻¹ = 1 ∧
    PowerSeries.constantCoeff (logZ M) = 0 ∧
    PowerSeries.derivative (R := ℂ) (detSeries M)⁻¹ =
      (detSeries M)⁻¹ * PowerSeries.derivative (R := ℂ) (logZ M) ∧
    ∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 1 →
      PowerSeries.derivative (R := ℂ) Q = Q * PowerSeries.derivative (R := ℂ) (logZ M) →
      Q = (detSeries M)⁻¹ := by
  obtain ⟨hP, hL0, hP0⟩ := logdet_eq_log M
  have hPd : PowerSeries.derivative (R := ℂ) (detSeries M) =
      detSeries M * PowerSeries.derivative (R := ℂ) (logSeries M) := hP
  have hP0' : PowerSeries.constantCoeff (detSeries M) = 1 := hP0
  have hne : PowerSeries.constantCoeff (detSeries M) ≠ 0 := by rw [hP0']; exact one_ne_zero
  have hZP : (detSeries M)⁻¹ * detSeries M = 1 := PowerSeries.inv_mul_cancel _ hne
  have hPZ : detSeries M * (detSeries M)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hne
  refine ⟨hZP, by rw [PowerSeries.constantCoeff_inv, hP0', inv_one], ?_, ?_, ?_⟩
  · rw [logZ_eq_neg, map_neg, hL0, neg_zero]
  · rw [PowerSeries.derivative_inv', hPd, logZ_eq_neg, map_neg]
    linear_combination (-((detSeries M)⁻¹ * PowerSeries.derivative (R := ℂ) (logSeries M))) * hZP
  · intro Q hQ0 hQ
    have hQne : PowerSeries.constantCoeff Q ≠ 0 := by rw [hQ0]; exact one_ne_zero
    have hQQ : Q⁻¹ * Q = 1 := PowerSeries.inv_mul_cancel _ hQne
    have hQQ' : Q * Q⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hQne
    have hinv : PowerSeries.derivative (R := ℂ) Q⁻¹ =
        Q⁻¹ * PowerSeries.derivative (R := ℂ) (logSeries M) := by
      rw [PowerSeries.derivative_inv', hQ, logZ_eq_neg, map_neg]
      linear_combination (Q⁻¹ * PowerSeries.derivative (R := ℂ) (logSeries M)) * hQQ
    have hQinv0 : PowerSeries.constantCoeff Q⁻¹ = 1 := by
      rw [PowerSeries.constantCoeff_inv, hQ0, inv_one]
    have hu : Q⁻¹ = detSeries M := log_unique M Q⁻¹ hinv hQinv0
    calc Q = Q * (detSeries M * (detSeries M)⁻¹) := by rw [hPZ, mul_one]
      _ = Q * Q⁻¹ * (detSeries M)⁻¹ := by rw [← hu]; ring
      _ = (detSeries M)⁻¹ := by rw [hQQ', one_mul]

/-- `Γ = −log Z = log det(I − uM)` (`logSeries`, `Existence/LogDet.lean`). -/
theorem effAction_eq (M : Matrix ι ι ℂ) : -logZ M = logSeries M := by
  rw [logZ_eq_neg, neg_neg]

end LogZ

/-! ## The closed walks and their holonomy -/

section Histories

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The step with a connection, entry by entry:** `B[U](S′, s; S, t) = [s ≠ t][S′ = S △ T_s] U_{S′S}`. -/
theorem Bconn_apply (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (y : Fin 16) (i : n) (s : Fin 5)
    (x : Fin 16) (j : n) (t : Fin 5) :
    Bconn c ((y, i), s) ((x, j), t) =
      if s ≠ t ∧ y = transition s x then (c.U y x : Matrix n n ℂ) i j else 0 := by
  simp only [Bconn, stepOp, Matrix.of_apply, WholePicture.connStep, WholePicture.turnMat]
  by_cases h1 : s = t
  · simp [h1]
  · by_cases h2 : y = transition s x <;> simp [h1, h2]

/-- The eighty states with the internal index outside: `((x, i), s) ↦ ((x, s), i)`. -/
def stateEquiv (n : Type*) : (Fin 16 × n) × Fin 5 ≃ State × n where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `B[U]` with the internal index outside. -/
noncomputable def BconnS (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) :
    Matrix (State × n) (State × n) ℂ :=
  Matrix.reindex (stateEquiv n) (stateEquiv n) (Bconn c)

theorem trace_reindex_eq {m' n' : Type*} [Fintype m'] [Fintype n'] (e : m' ≃ n')
    (M : Matrix m' m' ℂ) : (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

theorem BconnS_pow (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (r : ℕ) :
    (BconnS c) ^ r = Matrix.reindex (stateEquiv n) (stateEquiv n) ((Bconn c) ^ r) := by
  have h := map_pow (Matrix.reindexAlgEquiv ℂ ℂ (stateEquiv n)) (Bconn c) r
  simp only [Matrix.coe_reindexAlgEquiv] at h
  rw [BconnS, h]

/-- The block of `B[U]` from the state `a` to the state `a′`: the rotation `U_{a′a}` if `a′` continues `a`. -/
theorem blk_BconnS_apply (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (a' a : State) (i' i : n) :
    blk (BconnS c) a' a i' i =
      if Continues a a' then WholePicture.turnMat c a'.1 a.1 i' i else 0 := by
  simp only [blk, BconnS, Matrix.reindex_apply, Matrix.submatrix_apply, stateEquiv,
    Equiv.coe_fn_symm_mk, Bconn, stepOp, Matrix.of_apply, WholePicture.connStep, Continues]
  by_cases h1 : a'.2 = a.2
  · simp [h1]
  · by_cases h2 : a'.1 = transition a'.2 a.1 <;> simp [h1, h2]

/-- A word of states is **a closed walk** when each state continues the one before, the first
continuing the last. -/
def IsClosedHistory {r : ℕ} (hr : 0 < r) (w : Fin r → State) : Prop :=
  ∀ j : Fin r, Continues (w j) (ext hr w (j.1 + 1))

instance {r : ℕ} (hr : 0 < r) : DecidablePred (IsClosedHistory hr) := fun w => by
  unfold IsClosedHistory; infer_instance

theorem holL_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℕ → Matrix ι ι ℂ) {j : ℕ}
    (h : A j = 0) : ∀ r, j < r → holL A r = 0
  | 0, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hj => by
    rw [holL_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · rw [holL_eq_zero A h r hlt, mul_zero]
    · rw [← heq, h, zero_mul]

theorem holL_congr {ι : Type*} [Fintype ι] [DecidableEq ι] (A A' : ℕ → Matrix ι ι ℂ) :
    ∀ r, (∀ j < r, A j = A' j) → holL A r = holL A' r
  | 0, _ => rfl
  | r + 1, h => by
    rw [holL_succ, holL_succ, h r (Nat.lt_succ_self r),
      holL_congr A A' r (fun j hj => h j (Nat.lt_succ_of_lt hj))]

/-- **The holonomy of a word of states:** the ordered product of the rotations along it when it is a closed
walk, and `0` otherwise. -/
theorem hol_BconnS (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) {r : ℕ} (hr : 0 < r)
    (w : Fin r → State) :
    GroupsContinuumLaw.Euler.hol (BconnS c) hr w = if IsClosedHistory hr w then
      holL (fun j => WholePicture.turnMat c (ext hr w (j + 1)).1 (ext hr w j).1) r else 0 := by
  split_ifs with h
  · apply holL_congr
    intro j hj
    have hc : Continues (ext hr w j) (ext hr w (j + 1)) := by
      have h' := h ⟨j, hj⟩
      rw [← ext_lt hr w ⟨j, hj⟩] at h'
      exact h'
    ext i' i
    rw [blk_BconnS_apply, if_pos hc]
  · simp only [IsClosedHistory, not_forall] at h
    obtain ⟨j, hj⟩ := h
    apply holL_eq_zero _ (j := j.1) _ r j.2
    ext i' i
    rw [blk_BconnS_apply, ext_lt hr w j, if_neg hj, Matrix.zero_apply]

/-- **`Tr B[U]^r` is the sum over the closed walks of length `r` of the trace of their holonomy.** -/
theorem trace_Bconn_pow (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) {r : ℕ} (hr : 0 < r) :
    ((Bconn c) ^ r).trace = ∑ w : Fin r → State,
      if IsClosedHistory hr w then
        (holL (fun j => WholePicture.turnMat c (ext hr w (j + 1)).1 (ext hr w j).1) r).trace
      else 0 := by
  rw [← trace_reindex_eq (stateEquiv n), ← BconnS_pow, trace_pow_block (BconnS c) hr]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hol_BconnS]
  split_ifs <;> simp

/-- **Every closed walk counted once, with its holonomy:** the coefficient of `uʳ` of
`log Z = Σ_r uʳ Tr B[U]^r/r` is that of `Σ_{ℓ primitive} (1/|ℓ|) Σ_k u^{k|ℓ|} Tr(hol ℓ)^k/k`. -/
theorem euler_Bconn (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) {r : ℕ} (hr : 0 < r) :
    ((Bconn c) ^ r).trace / r = ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter
        fun p : Fin d.1 → State => minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
      (1 / (d.1 : ℂ)) * (((GroupsContinuumLaw.Euler.hol (BconnS c) (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1)).trace /
        ((r / d.1 : ℕ) : ℂ)) := by
  rw [← trace_reindex_eq (stateEquiv n), ← BconnS_pow]
  exact euler_holonomy_log (BconnS c) hr

end Histories

/-! ## The weight of a step -/

/-- **Each state has four continuations:** `B𝟏 = 4·𝟏`. -/
theorem B_mulVec_one : (B ℂ) *ᵥ (fun _ => (1 : ℂ)) = fun _ => 4 := by
  funext s'
  simp only [Matrix.mulVec, dotProduct, B_apply, mul_one, Finset.sum_boole]
  rw [card_predecessors s']
  norm_num

/-- **`(uB)𝟏 = 𝟏` exactly at `u = 1/4`.** -/
theorem quarter_iff (u : ℂ) : (u • B ℂ) *ᵥ (fun _ => (1 : ℂ)) = (fun _ => 1) ↔ u = 1 / 4 := by
  rw [Matrix.smul_mulVec, B_mulVec_one]
  constructor
  · intro h
    have h0 := congrFun h ((0 : Fin 16), (0 : Fin 5))
    simp only [Pi.smul_apply, smul_eq_mul] at h0
    linear_combination h0 / 4
  · rintro rfl
    funext s
    simp only [Pi.smul_apply, smul_eq_mul]
    norm_num

/-- **`B/4` is a walk:** its entries are `0` or `1/4` and each row of continuations sums to one. -/
theorem quarter_walk :
    (∀ p q : State, 0 ≤ ((1 / 4 : ℝ) • B ℝ) p q) ∧
      (∀ s : State, ∑ s' : State, ((1 / 4 : ℝ) • B ℝ) s' s = 1) := by
  refine ⟨fun p q => ?_, fun s => ?_⟩
  · simp only [Matrix.smul_apply, B_apply, smul_eq_mul]
    split_ifs <;> norm_num
  · simp only [Matrix.smul_apply, B_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_boole]
    rw [card_continuations s]
    norm_num

end Law

open Comparison.System.Law

/-- **Equation (12):** for every unitary connection `U`, `Z = det(I − uB[U])⁻¹` and
`log Z = Σ_{r ≥ 1} uʳ Tr B[U]^r/r`, as formal power series in `u` (`det(I − uB[U])` is the polynomial whose value
at every `u` is the determinant): `Z·det(I − uB[U]) = 1`, `Z(0) = 1`, `(log Z)(0) = 0`, `Z′ = Z·(log Z)′`, and
`Z` is the only power series with `Z(0) = 1` and this logarithmic derivative.
Every candidate system: System.uniqueness. -/
theorem eq_12 (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) :
    (∀ u : ℂ, (1 - u • Bconn c).det =
      ((1 - (Polynomial.X : Polynomial ℂ) • (Bconn c).map Polynomial.C).det).eval u) ∧
    (detSeries (Bconn c))⁻¹ * detSeries (Bconn c) = 1 ∧
    PowerSeries.constantCoeff (detSeries (Bconn c))⁻¹ = 1 ∧
    PowerSeries.constantCoeff (logZ (Bconn c)) = 0 ∧
    PowerSeries.derivative (R := ℂ) (detSeries (Bconn c))⁻¹ =
      (detSeries (Bconn c))⁻¹ * PowerSeries.derivative (R := ℂ) (logZ (Bconn c)) ∧
    (∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 1 →
      PowerSeries.derivative (R := ℂ) Q = Q * PowerSeries.derivative (R := ℂ) (logZ (Bconn c)) →
      Q = (detSeries (Bconn c))⁻¹) :=
  ⟨det_one_sub_smul_poly (Bconn c), log_Z (Bconn c)⟩

/-- **Proposition 52, every closed walk counted once.** For every unitary connection `U`:
`B[U](S′, s; S, t) = [s ≠ t][S′ = S △ T_s] U_{S′S}`; `Tr B[U]^r` is the sum, over the closed walks of length `r`
with a marked first step, of the trace of their holonomy (the ordered product of the rotations), every other word of
states having holonomy zero; `Tr B[U]^r/r = Σ_{d∣r} Σ_{ℓ primitive, |ℓ|=d} (1/d) Tr(hol ℓ)^{r/d}/(r/d)`, which is
the coefficient of `uʳ` of `−Σ_{[ℓ]} log det(1 − u^{|ℓ|} hol ℓ)` with each primitive class counted once;
`log Z = Σ_r uʳ Tr B[U]^r/r` with `Z = det(I − uB[U])⁻¹` (equation (12)), and `Γ = −log Z = log det(I − uB[U])`;
each state has four continuations, `(uB)𝟏 = 𝟏 ⟺ u = 1/4`, and `B/4` is a walk.
Recognition: `Z` is the partition function of the closed walks, `Γ` its effective action; `B/4` is the walk of
Prop. 26. Every candidate system: System.uniqueness. -/
theorem prop_52 :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)),
      (∀ (y : Fin 16) (i : n) (s : Fin 5) (x : Fin 16) (j : n) (t : Fin 5),
        Bconn c ((y, i), s) ((x, j), t) =
          if s ≠ t ∧ y = transition s x then (c.U y x : Matrix n n ℂ) i j else 0) ∧
      (∀ (r : ℕ) (hr : 0 < r) (w : Fin r → State), GroupsContinuumLaw.Euler.hol (BconnS c) hr w =
        if IsClosedHistory hr w then
          holL (fun j => WholePicture.turnMat c (ext hr w (j + 1)).1 (ext hr w j).1) r else 0) ∧
      (∀ (r : ℕ) (hr : 0 < r), ((Bconn c) ^ r).trace = ∑ w : Fin r → State,
        if IsClosedHistory hr w then
          (holL (fun j => WholePicture.turnMat c (ext hr w (j + 1)).1 (ext hr w j).1) r).trace
        else 0) ∧
      (∀ (r : ℕ) (hr : 0 < r), ((Bconn c) ^ r).trace / r = ∑ d ∈ r.divisors.attach,
        ∑ p ∈ (Finset.univ.filter
          fun p : Fin d.1 → State => minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
        (1 / (d.1 : ℂ)) * (((GroupsContinuumLaw.Euler.hol (BconnS c) (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1)).trace /
          ((r / d.1 : ℕ) : ℂ))) ∧
      (detSeries (Bconn c))⁻¹ * detSeries (Bconn c) = 1 ∧
      PowerSeries.constantCoeff (detSeries (Bconn c))⁻¹ = 1 ∧
      PowerSeries.constantCoeff (logZ (Bconn c)) = 0 ∧
      PowerSeries.derivative (R := ℂ) (detSeries (Bconn c))⁻¹ =
        (detSeries (Bconn c))⁻¹ * PowerSeries.derivative (R := ℂ) (logZ (Bconn c)) ∧
      (∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 1 →
        PowerSeries.derivative (R := ℂ) Q = Q * PowerSeries.derivative (R := ℂ) (logZ (Bconn c)) →
        Q = (detSeries (Bconn c))⁻¹) ∧
      -logZ (Bconn c) = logSeries (Bconn c)) ∧
    (∀ s : State, (Finset.univ.filter (Continues s)).card = 4) ∧
    (B ℂ) *ᵥ (fun _ => (1 : ℂ)) = (fun _ => 4) ∧
    (∀ u : ℂ, (u • B ℂ) *ᵥ (fun _ => (1 : ℂ)) = (fun _ => 1) ↔ u = 1 / 4) ∧
    (∀ p q : State, 0 ≤ ((1 / 4 : ℝ) • B ℝ) p q) ∧
    (∀ s : State, ∑ s' : State, ((1 / 4 : ℝ) • B ℝ) s' s = 1) := by
  refine ⟨fun n _ _ c => ⟨Bconn_apply c, fun r hr w => hol_BconnS c hr w,
      fun r hr => trace_Bconn_pow c hr, fun r hr => euler_Bconn c hr, ?_⟩,
    card_continuations, B_mulVec_one, quarter_iff, quarter_walk.1, quarter_walk.2⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := log_Z (Bconn c)
  exact ⟨h1, h2, h3, h4, h5, effAction_eq (Bconn c)⟩

end Comparison.System
