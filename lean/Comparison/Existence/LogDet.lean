module

public import Mathlib

/-!
# Book X. Every closed walk counted once: `log det(I − uB) = −Σ_r uʳ tr Bʳ/r` (Proposition 52)

For any square matrix `B` over a
commutative ring, `P(u) = det(I − uB)` is a polynomial with `P(0) = 1`.

* `derivative_det`: **Jacobi's formula** for a matrix of polynomials, `(det M)' = tr(adj M · M')`.
* `derivative_det_one_sub`: `P' = −tr(adj(I − uB) B)`.
* `geomSeries B = Σ_r uʳBʳ`; `one_sub_mul_geomSeries`: `(I − uB) Σ_r uʳBʳ = I` in power series.
* `logdet_derivative`: **`P' = −P · Σ_{r ≥ 0} uʳ tr B^{r+1}`** as formal power series: the
  logarithmic derivative of `det(I − uB)` is `−Σ_r uʳ tr B^{r+1}`.
* `logSeries B = −Σ_{r ≥ 1} uʳ tr Bʳ / r` over a field of characteristic zero; `logdet_eq_log`:
  **`P' = P · L'`, `L(0) = 0`, `P(0) = 1`**, and `log_unique`: `P` is the only power series with
  constant term `1` whose logarithmic derivative is `L'`. That is, `log det(I − uB) = L` as formal
  power series.
-/

@[expose] public section

namespace Comparison

open Polynomial Matrix

section Jacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem prod_updateCol (M : Matrix n n R) (i : n) (v : n → R) (σ : Equiv.Perm n) :
    ∏ j, (M.updateCol i v) (σ j) j = (∏ j ∈ Finset.univ.erase i, M (σ j) j) * v (σ i) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [updateCol_apply, if_neg (Finset.ne_of_mem_erase hj)]
  · rw [updateCol_self]

/-- **Jacobi's formula:** `(det M)' = tr(adj M · M')` for a matrix of polynomials. -/
theorem derivative_det (M : Matrix n n R[X]) :
    derivative M.det = (M.adjugate * M.map derivative).trace := by
  have rhs : (M.adjugate * M.map derivative).trace =
      ∑ i, (M.updateCol i (fun k => derivative (M k i))).det := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diag]
  rw [rhs]
  simp only [det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivative_prod_finset, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prod_updateCol, Units.smul_def]

theorem map_derivative_one_sub (B : Matrix n n R) :
    (1 - (X : R[X]) • B.map C).map derivative = -(B.map C) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h]

/-- `P' = −tr(adj(I − uB) B)`. -/
theorem derivative_det_one_sub (B : Matrix n n R) :
    derivative (1 - (X : R[X]) • B.map C).det =
      -((1 - (X : R[X]) • B.map C).adjugate * B.map C).trace := by
  rw [derivative_det, map_derivative_one_sub, Matrix.mul_neg, Matrix.trace_neg]

end Jacobi

section Series

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- `Σ_r uʳ Bʳ`, a matrix of power series. -/
noncomputable def geomSeries (B : Matrix n n R) : Matrix n n (PowerSeries R) :=
  Matrix.of fun i j => PowerSeries.mk fun r => (B ^ r) i j

/-- `I − uB` read in power series. -/
noncomputable def oneSubPS (B : Matrix n n R) : Matrix n n (PowerSeries R) :=
  1 - (PowerSeries.X (R := R)) • B.map (PowerSeries.C (R := R))

theorem mapMatrix_C (B : Matrix n n R) :
    (Polynomial.coeToPowerSeries.ringHom : R[X] →+* PowerSeries R).mapMatrix (B.map C) =
      B.map (PowerSeries.C (R := R)) := by
  ext i j
  simp

theorem oneSubPS_eq (B : Matrix n n R) :
    (Polynomial.coeToPowerSeries.ringHom : R[X] →+* PowerSeries R).mapMatrix
      (1 - (X : R[X]) • B.map C) = oneSubPS B := by
  rw [map_sub, map_one, oneSubPS]
  congr 1
  ext i j
  simp <;> ring

/-- **`(I − uB) Σ_r uʳBʳ = I`.** -/
theorem one_sub_mul_geomSeries (B : Matrix n n R) : oneSubPS B * geomSeries B = 1 := by
  ext i j r
  rw [oneSubPS, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul,
    Matrix.smul_apply, map_sub, smul_eq_mul]
  rcases r with _ | r
  · simp [geomSeries, PowerSeries.coeff_mk, Matrix.one_apply]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [geomSeries, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, map_sum,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [pow_succ', Matrix.mul_apply, sub_self]
    simp only [Matrix.one_apply]
    split_ifs <;> simp [PowerSeries.coeff_one]

/-- The adjugate of `I − uB` is `det(I − uB) · Σ_r uʳBʳ`. -/
theorem adjugate_oneSubPS (B : Matrix n n R) :
    (oneSubPS B).adjugate = (oneSubPS B).det • geomSeries B := by
  calc (oneSubPS B).adjugate = (oneSubPS B).adjugate * (oneSubPS B * geomSeries B) := by
        rw [one_sub_mul_geomSeries, Matrix.mul_one]
    _ = ((oneSubPS B).adjugate * oneSubPS B) * geomSeries B := by rw [Matrix.mul_assoc]
    _ = (oneSubPS B).det • geomSeries B := by rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

theorem trace_geomSeries_mul (B : Matrix n n R) :
    (geomSeries B * B.map (PowerSeries.C (R := R))).trace =
      PowerSeries.mk fun r => (B ^ (r + 1)).trace := by
  ext r
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, geomSeries, Matrix.of_apply,
    Matrix.map_apply, map_sum, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]

theorem map_trace_coe (M : Matrix n n R[X]) :
    (Polynomial.coeToPowerSeries.ringHom : R[X] →+* PowerSeries R) M.trace =
      ((Polynomial.coeToPowerSeries.ringHom : R[X] →+* PowerSeries R).mapMatrix M).trace := by
  simp [Matrix.trace, map_sum]

/-- **The logarithmic derivative of `det(I − uB)`:** `P' = −P · Σ_{r ≥ 0} uʳ tr B^{r+1}`. -/
theorem logdet_derivative (B : Matrix n n R) :
    PowerSeries.derivative (R := R) ((1 - (X : R[X]) • B.map C).det : PowerSeries R) =
      -(((1 - (X : R[X]) • B.map C).det : PowerSeries R) *
        PowerSeries.mk fun r => (B ^ (r + 1)).trace) := by
  have hc : ∀ p : R[X], (p : PowerSeries R) =
      (Polynomial.coeToPowerSeries.ringHom : R[X] →+* PowerSeries R) p := fun p => rfl
  rw [PowerSeries.derivative_coe, derivative_det_one_sub, hc, hc, map_neg, map_trace_coe, map_mul,
    RingHom.map_adjugate, oneSubPS_eq, mapMatrix_C, adjugate_oneSubPS, Matrix.smul_mul,
    Matrix.trace_smul, trace_geomSeries_mul, smul_eq_mul, RingHom.map_det, oneSubPS_eq]

theorem constantCoeff_det_one_sub (B : Matrix n n R) :
    PowerSeries.constantCoeff ((1 - (X : R[X]) • B.map C).det : PowerSeries R) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  exact B.eval_charpolyRev

end Series

section Log

variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **`L = −Σ_{r ≥ 1} uʳ tr Bʳ / r`.** -/
noncomputable def logSeries (B : Matrix n n K) : PowerSeries K :=
  PowerSeries.mk fun r => if r = 0 then 0 else -(B ^ r).trace / r

theorem derivative_logSeries (B : Matrix n n K) :
    PowerSeries.derivative (R := K) (logSeries B) =
      -PowerSeries.mk fun r => (B ^ (r + 1)).trace := by
  ext r
  rw [PowerSeries.coeff_derivative, logSeries, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero r),
    map_neg, PowerSeries.coeff_mk]
  have h : ((r : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  push_cast
  field_simp

/-- **`log det(I − uB) = L`:** `P' = P · L'`, `L(0) = 0`, `P(0) = 1`. -/
theorem logdet_eq_log (B : Matrix n n K) :
    PowerSeries.derivative (R := K) ((1 - (X : K[X]) • B.map C).det : PowerSeries K) =
        ((1 - (X : K[X]) • B.map C).det : PowerSeries K) *
          PowerSeries.derivative (R := K) (logSeries B) ∧
      PowerSeries.constantCoeff (logSeries B) = 0 ∧
      PowerSeries.constantCoeff ((1 - (X : K[X]) • B.map C).det : PowerSeries K) = 1 := by
  refine ⟨?_, ?_, constantCoeff_det_one_sub B⟩
  · rw [logdet_derivative, derivative_logSeries, mul_neg]
  · rw [logSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      if_pos rfl]

/-- **The logarithm determines the series:** `det(I − uB)` is the only power series with constant
term `1` whose logarithmic derivative is `L'`. -/
theorem log_unique (B : Matrix n n K) (Q : PowerSeries K)
    (hQ : PowerSeries.derivative (R := K) Q = Q * PowerSeries.derivative (R := K) (logSeries B))
    (hQ0 : PowerSeries.constantCoeff Q = 1) :
    Q = ((1 - (X : K[X]) • B.map C).det : PowerSeries K) := by
  obtain ⟨hP, -, hP0⟩ := logdet_eq_log B
  set P : PowerSeries K := ((1 - (X : K[X]) • B.map C).det : PowerSeries K) with hPdef
  have hunit : IsUnit P := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hP0]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hunit
  set v : PowerSeries K := ((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) with hv
  have hvu : v * P = 1 := by
    rw [hv, ← hu]
    exact u.inv_mul
  have hDv : PowerSeries.derivative (R := K) v = -(v ^ 2) * PowerSeries.derivative (R := K) P := by
    rw [hv, PowerSeries.derivative_inv, hu]
  have hD : PowerSeries.derivative (R := K) (Q * v) =
      PowerSeries.derivative (R := K) (1 : PowerSeries K) := by
    rw [Derivation.leibniz, hDv, hQ, hP, PowerSeries.derivative_one, smul_eq_mul, smul_eq_mul]
    linear_combination (-(Q * v * PowerSeries.derivative (R := K) (logSeries B))) * hvu
  have hc : PowerSeries.constantCoeff (Q * v) = PowerSeries.constantCoeff (1 : PowerSeries K) := by
    have h1 : PowerSeries.constantCoeff v * PowerSeries.constantCoeff P = 1 := by
      rw [← map_mul, hvu, map_one]
    rw [hP0, mul_one] at h1
    rw [map_mul, hQ0, one_mul, map_one, h1]
  have h := PowerSeries.derivative.ext hD hc
  calc Q = Q * v * P := by rw [mul_assoc, hvu, mul_one]
    _ = P := by rw [h, one_mul]

end Log

end Comparison

end
