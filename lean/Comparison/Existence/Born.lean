module

public import Comparison.Existence.IharaBass

/-!
# Book X. Probability: the first mixed coefficient of the doubled operator (Proposition 58)

`K` an invertible operator,
`G = K⁻¹`, a preparation `X` and a detection `Y` (any numbers of columns).

* `doubled K X Y s t = 𝔻(s, t) = [[K, −sXX†], [−tYY†, K†]]`; `bornM = G†YY†GXX†`.
* `doubled_det`: **`det 𝔻(s, t) = det K · det K† · det(1 − ts G†YY†GXX†)`** (Proposition 57).
* `bornM_trace`: **`tr(G†YY†GXX†) = ‖Y†GX‖² = Σ |(Y†GX)_ij|²`**, a non-negative real number.
* `det_coeff_one`: the coefficient of `x` in `det(1 − xM)` is `−tr M`.
* `log_doubled`: `−log det 𝔻(s, t) = −log |det K|² − log det(1 − ts M)` while `det(1 − tsM)` stays in
  the slit plane.
* `born_log_deriv`, `born_mixed`: **`∂_s∂_t[−log det 𝔻]_{s=t=0} = tr(G†YY†GXX†) = ‖Y†GX‖²`**: for
  every `s`, `∂_t[−log det(1 − stM)]_{t=0} = s·tr M`, whose `s`-derivative is `tr M`.
-/

@[expose] public section

namespace Comparison

open Matrix

section Born

variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]
  [DecidableEq q]

/-- **The doubled operator** `𝔻(s, t) = [[K, −sXX†], [−tYY†, K†]]`. -/
def doubled (K : Matrix n n ℂ) (X : Matrix n p ℂ) (Y : Matrix n q ℂ) (s t : ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks K (-(s • (X * Xᴴ))) (-(t • (Y * Yᴴ))) Kᴴ

/-- `M = G†YY†GXX†` with `G = K⁻¹`. -/
def bornM (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ) :
    Matrix n n ℂ :=
  (⅟K)ᴴ * (Y * Yᴴ) * ⅟K * (X * Xᴴ)

/-- **`det 𝔻(s, t) = det K · det K† · det(1 − ts M)`.** -/
theorem doubled_det (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (s t : ℂ) : (doubled K X Y s t).det = K.det * Kᴴ.det * (1 - (t * s) • bornM K X Y).det := by
  rw [doubled, det_fromBlocks₁₁]
  have hKK : Kᴴ * (⅟K)ᴴ = 1 := by rw [← conjTranspose_mul, invOf_mul_self, conjTranspose_one]
  have hK' : ∀ Z : Matrix n n ℂ, Kᴴ * ((⅟K)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hKK, Matrix.one_mul]
  have e : Kᴴ - -(t • (Y * Yᴴ)) * ⅟K * -(s • (X * Xᴴ)) = Kᴴ * (1 - (t * s) • bornM K X Y) := by
    simp only [bornM, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hK']
    module
  rw [e, det_mul, mul_assoc]

/-- **`tr(G†YY†GXX†) = ‖Y†GX‖²`.** -/
theorem bornM_trace (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ) :
    (bornM K X Y).trace =
      ((∑ i, ∑ j, Complex.normSq ((Yᴴ * ⅟K * X) i j) : ℝ) : ℂ) := by
  have hW : (bornM K X Y).trace = ((Yᴴ * ⅟K * X)ᴴ * (Yᴴ * ⅟K * X)).trace := by
    rw [bornM, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm Xᴴ]
    simp only [Matrix.mul_assoc]
  rw [hW, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- The trace is real and not negative. -/
theorem bornM_trace_nonneg (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ)
    (Y : Matrix n q ℂ) :
    0 ≤ ∑ i, ∑ j, Complex.normSq ((Yᴴ * ⅟K * X) i j) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The coefficient of `x` in `det(1 − xM)` is `−tr M`. -/
theorem det_coeff_one (M : Matrix n n ℂ) :
    ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det).coeff 1 = -M.trace :=
  M.coeff_charpolyRev_eq_neg_trace

/-- **`d/dx[−log det(1 − xM)]` at `0` is `tr M`.** -/
theorem born_log_deriv (M : Matrix n n ℂ) :
    HasDerivAt (fun x : ℂ => -Complex.log (1 - x • M).det) M.trace 0 := by
  have hf : (fun x : ℂ => (1 - x • M).det) =
      fun x => ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det).eval x := by
    funext x
    exact det_one_sub_smul_poly M x
  have hP : HasDerivAt
      (fun x => ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det).eval x)
      (-M.trace) 0 := by
    have h := ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det).hasDerivAt 0
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] at h
    simp only [Nat.cast_zero, zero_add, mul_one] at h
    rwa [det_coeff_one] at h
  have h0 : (1 - (0 : ℂ) • M).det = 1 := by simp
  have hlog := (hf ▸ hP).clog (by rw [h0]; exact Complex.one_mem_slitPlane)
  have := hlog.neg
  simp only [h0, div_one, neg_neg] at this
  exact this

/-- **The first mixed coefficient:** for every `s`, `∂_t[−log det(1 − stM)]_{t=0} = s·tr M`, and the
`s`-derivative of that at `0` is `tr M`. -/
theorem born_mixed (M : Matrix n n ℂ) :
    (∀ s : ℂ, HasDerivAt (fun t : ℂ => -Complex.log (1 - (s * t) • M).det) (s * M.trace) 0) ∧
      HasDerivAt (fun s : ℂ => s * M.trace) M.trace 0 := by
  refine ⟨fun s => ?_, ?_⟩
  · have hin : HasDerivAt (fun t : ℂ => s * t) s 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul s
    have h := (born_log_deriv M).comp_of_eq (hh := hin) (hy := by simp)
    simpa [Function.comp_def, mul_comm] using h
  · simpa using (hasDerivAt_id (0 : ℂ)).mul_const M.trace

/-- `det K · det K† = |det K|²`. -/
theorem det_mul_det_conjTranspose (K : Matrix n n ℂ) :
    K.det * Kᴴ.det = ((Complex.normSq K.det : ℝ) : ℂ) := by
  rw [det_conjTranspose, Complex.normSq_eq_conj_mul_self, mul_comm]
  rfl

/-- **`−log det 𝔻(s, t) = −log |det K|² − log det(1 − ts M)`.** -/
theorem log_doubled (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (s t : ℂ) (hne : (1 - (t * s) • bornM K X Y).det ≠ 0) :
    -Complex.log (doubled K X Y s t).det =
      -(Real.log (Complex.normSq K.det) : ℂ) - Complex.log (1 - (t * s) • bornM K X Y).det := by
  have hK : K.det ≠ 0 := (isUnit_det_of_invertible K).ne_zero
  have hpos : 0 < Complex.normSq K.det := Complex.normSq_pos.mpr hK
  rw [doubled_det, det_mul_det_conjTranspose, mul_comm, Complex.log_mul_ofReal _ hpos _ hne]
  ring

end Born

end Comparison

end
