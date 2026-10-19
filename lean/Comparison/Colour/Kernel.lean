module

public import Mathlib

/-!
# Book XIII. One two-line kernel (Proposition 76)

The rotations of the three colour lines
are `su(3)`; `gen3 a = λ_a/2` with the eight Gell-Mann matrices `λ_a` (`gellMann`; the eighth is
`(1/√3) diag(1, 1, −2)`).

* `gen3_conjTranspose`, `gen3_trace`: Hermitian and of trace zero; `gen3_trace_mul`:
  `Tr T^aT^b = δ_ab/2`.
* `fierz`: `Σ_a T^a_ij T^a_kl = ½(δ_il δ_jk − ⅓ δ_ij δ_kl)`.
* `casimir`: **`C_F = Σ_a T^aT^a = (4/3)·1`**.
* `meson_pair`: a line and its conjugate (generators `−T^a*`) on `δ`: **`T₁·T₂ = −4/3`**.
* `pair_eq`: on two lines `Σ_a T^a ⊗ T^a = ½(P − ⅓)`; `pair_antisymm`: **`−2/3`** on every
  antisymmetric pair (the pairs inside `ε`); `pair_symm`: **`+1/3`** on every symmetric pair.
* `baryon_line`: on `ε`, each line's two pairs give **`−2/3 − 2/3 = −4/3 = −C_F`**, as in the meson.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex

/-- `1/√3`, a real number. -/
noncomputable def invSqrt3 : ℂ := ((Real.sqrt 3)⁻¹ : ℝ)

theorem invSqrt3_mul_self : invSqrt3 * invSqrt3 = 1 / 3 := by
  rw [invSqrt3, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

theorem star_invSqrt3 : star invSqrt3 = invSqrt3 := by
  rw [invSqrt3, Complex.star_def, Complex.conj_ofReal]

/-- `diag(1, 1, −2)`. -/
def d8 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, -2]

/-- The first seven Gell-Mann matrices. -/
def gellMann7 : Fin 7 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 1, 0; 1, 0, 0; 0, 0, 0], !![0, -I, 0; I, 0, 0; 0, 0, 0], !![1, 0, 0; 0, -1, 0; 0, 0, 0],
    !![0, 0, 1; 0, 0, 0; 1, 0, 0], !![0, 0, -I; 0, 0, 0; I, 0, 0], !![0, 0, 0; 0, 0, 1; 0, 1, 0],
    !![0, 0, 0; 0, 0, -I; 0, I, 0]]

/-- The eight Gell-Mann matrices: the seven, and `(1/√3) diag(1, 1, −2)`. -/
noncomputable def gellMann (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  Fin.lastCases (invSqrt3 • d8) gellMann7 a

/-- **The rotations of the colour lines:** `T^a = λ_a/2`. -/
noncomputable def gen3 (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ := (1 / 2 : ℂ) • gellMann a

theorem gen3_castSucc (a : Fin 7) : gen3 (Fin.castSucc a) = (1 / 2 : ℂ) • gellMann7 a := by
  simp [gen3, gellMann]

theorem gen3_last : gen3 (Fin.last 7) = (invSqrt3 / 2) • d8 := by
  rw [gen3, gellMann, Fin.lastCases_last, smul_smul]
  congr 1
  ring

/-- A sum over the eight rotations: the seven and the eighth. -/
theorem sum_gen3 (f : Matrix (Fin 3) (Fin 3) ℂ → ℂ) :
    ∑ a, f (gen3 a) = ∑ a : Fin 7, f ((1 / 2 : ℂ) • gellMann7 a) + f ((invSqrt3 / 2) • d8) := by
  rw [Fin.sum_univ_castSucc]
  simp only [gen3_castSucc, gen3_last]

theorem last_mul (i j k l : Fin 3) :
    ((invSqrt3 / 2) • d8) i j * ((invSqrt3 / 2) • d8) k l = (1 / 12) * (d8 i j * d8 k l) := by
  simp only [Matrix.smul_apply, smul_eq_mul]
  have e : invSqrt3 / 2 * d8 i j * (invSqrt3 / 2 * d8 k l) =
      (invSqrt3 * invSqrt3) / 4 * (d8 i j * d8 k l) := by ring
  rw [e, invSqrt3_mul_self]
  ring

theorem last_mul_star (i j k l : Fin 3) :
    ((invSqrt3 / 2) • d8) i j * star (((invSqrt3 / 2) • d8) k l) =
      (1 / 12) * (d8 i j * d8 k l) := by
  have hs : star (((invSqrt3 / 2) • d8) k l) = ((invSqrt3 / 2) • d8) k l := by
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_div₀, star_invSqrt3]
    fin_cases k <;> fin_cases l <;> simp [d8]
  rw [hs, last_mul]

/-! ## Hermitian, of trace zero, orthonormal -/

theorem gen3_conjTranspose (a : Fin 8) : (gen3 a)ᴴ = gen3 a := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [gen3_last]
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
      star_div₀, star_invSqrt3]
    fin_cases i <;> fin_cases j <;> simp [d8]
  · rw [gen3_castSucc]
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [gellMann7]

theorem gen3_trace (a : Fin 8) : (gen3 a).trace = 0 := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [gen3_last]
    simp [Matrix.trace, Fin.sum_univ_three, d8]
  · rw [gen3_castSucc]
    fin_cases a <;> simp [gellMann7, Matrix.trace, Fin.sum_univ_three]

set_option maxHeartbeats 4000000 in
-- 64 pairs of rotations
/-- **`Tr T^aT^b = δ_ab/2`.** -/
theorem gen3_trace_mul (a b : Fin 8) :
    (gen3 a * gen3 b).trace = if a = b then 1 / 2 else 0 := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [gen3_last]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three, last_mul]
    simp [d8]
    norm_num
  · rw [gen3_last, gen3_castSucc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul]
    fin_cases b <;> simp [d8, gellMann7, Fin.ext_iff]
  · rw [gen3_last, gen3_castSucc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul]
    fin_cases a <;> simp [d8, gellMann7, Fin.ext_iff]
  · rw [gen3_castSucc, gen3_castSucc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul, Fin.castSucc_inj]
    fin_cases a <;> fin_cases b <;> simp [gellMann7, Complex.ext_iff] <;> norm_num

/-! ## The completeness of the eight rotations -/

set_option maxHeartbeats 8000000 in
-- 81 entries, each a sum over the eight rotations
/-- **`Σ_a T^a_ij T^a_kl = ½(δ_il δ_jk − ⅓ δ_ij δ_kl)`.** -/
theorem fierz (i j k l : Fin 3) :
    ∑ a, gen3 a i j * gen3 a k l =
      (1 / 2 : ℂ) * ((if i = l ∧ j = k then 1 else 0) -
        (1 / 3) * (if i = j ∧ k = l then 1 else 0)) := by
  rw [sum_gen3 (fun M => M i j * M k l)]
  simp only [last_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_seven, gellMann7, d8, Complex.ext_iff] <;> norm_num

/-- **The colour charge of a line:** `C_F = Σ_a T^aT^a = (4/3)·1`. -/
theorem casimir : ∑ a, gen3 a * gen3 a = (4 / 3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i l
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [fierz]
  fin_cases i <;> fin_cases l <;> simp [Fin.sum_univ_three] <;> norm_num

/-! ## A line and its conjugate -/

/-- The colour singlet of a line and its conjugate, `δ` (unnormalized). -/
def deltaVec : Fin 3 × Fin 3 → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- `T₁·T₂` on a line and its conjugate: the conjugate's rotations are `−T^a*`. -/
noncomputable def mesonPair : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => ∑ a, gen3 a p.1 q.1 * -star (gen3 a p.2 q.2)

theorem star_gen3 (a : Fin 8) (k l : Fin 3) : star (gen3 a k l) = gen3 a l k := by
  have := congrFun (congrFun (gen3_conjTranspose a) l) k
  rw [Matrix.conjTranspose_apply] at this
  exact this

/-- **A line and its conjugate in `δ`: `T₁·T₂ = −4/3`.** -/
theorem meson_pair : mesonPair *ᵥ deltaVec = (-4 / 3 : ℂ) • deltaVec := by
  ext ⟨i, k⟩
  have e : (mesonPair *ᵥ deltaVec) (i, k) = ∑ j, ∑ a, gen3 a i j * -star (gen3 a k j) := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mesonPair, Matrix.of_apply,
      deltaVec, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  rw [e]
  simp only [star_gen3, mul_neg, Finset.sum_neg_distrib, fierz]
  fin_cases i <;> fin_cases k <;> simp [deltaVec, Fin.sum_univ_three] <;> norm_num

/-! ## Two lines -/

/-- `T₁·T₂ = Σ_a T^a ⊗ T^a` on two lines. -/
noncomputable def pairOp : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => ∑ a, gen3 a p.1 q.1 * gen3 a p.2 q.2

/-- The swap of two lines. -/
def swap3 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- **`T₁·T₂ = ½(P − ⅓)` on two lines.** -/
theorem pair_eq : pairOp = (1 / 2 : ℂ) • (swap3 - (1 / 3 : ℂ) • 1) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [pairOp, Matrix.of_apply, fierz]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [swap3]

theorem swap3_mulVec (v : Fin 3 × Fin 3 → ℂ) : swap3 *ᵥ v = fun p => v (p.2, p.1) := by
  ext ⟨a, b⟩
  simp only [swap3, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

/-- **A pair inside `ε` (antisymmetric): `T₁·T₂ = −2/3`.** -/
theorem pair_antisymm (v : Fin 3 × Fin 3 → ℂ) (hv : ∀ a b, v (a, b) = -v (b, a)) :
    pairOp *ᵥ v = (-2 / 3 : ℂ) • v := by
  rw [pair_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    swap3_mulVec]
  ext ⟨a, b⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hv b a]
  ring

/-- **The symmetric pair: `T₁·T₂ = +1/3`.** -/
theorem pair_symm (v : Fin 3 × Fin 3 → ℂ) (hv : ∀ a b, v (a, b) = v (b, a)) :
    pairOp *ᵥ v = (1 / 3 : ℂ) • v := by
  rw [pair_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    swap3_mulVec]
  ext ⟨a, b⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hv b a]
  ring

/-! ## Three lines closed by `ε` -/

/-- The alternating symbol `ε_abc` on three colour ends. -/
def epsT (a b c : Fin 3) : ℂ :=
  if a = 0 ∧ b = 1 ∧ c = 2 ∨ a = 1 ∧ b = 2 ∧ c = 0 ∨ a = 2 ∧ b = 0 ∧ c = 1 then 1
  else if a = 1 ∧ b = 0 ∧ c = 2 ∨ a = 0 ∧ b = 2 ∧ c = 1 ∨ a = 2 ∧ b = 1 ∧ c = 0 then -1 else 0

/-- `T₁·T₂ = Σ_a T^a ⊗ T^a ⊗ 1` on the first two ends of three. -/
noncomputable def pair01 (T : Fin 3 → Fin 3 → Fin 3 → ℂ) : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun i j k => ∑ i', ∑ j', (∑ a, gen3 a i i' * gen3 a j j') * T i' j' k

/-- `T₁·T₃ = Σ_a T^a ⊗ 1 ⊗ T^a` on the first and third ends of three. -/
noncomputable def pair02 (T : Fin 3 → Fin 3 → Fin 3 → ℂ) : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun i j k => ∑ i', ∑ k', (∑ a, gen3 a i i' * gen3 a k k') * T i' j k'

theorem pair01_eq (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (i j k : Fin 3) :
    pair01 T i j k = (1 / 2 : ℂ) * (T j i k - (1 / 3) * T i j k) := by
  simp only [pair01, fierz]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

theorem pair02_eq (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (i j k : Fin 3) :
    pair02 T i j k = (1 / 2 : ℂ) * (T k j i - (1 / 3) * T i j k) := by
  simp only [pair02, fierz]
  fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- **Each line of `ε` holds `−C_F`:** its two pairs give `−2/3 − 2/3 = −4/3`, as the meson's one
pair does. -/
theorem baryon_line (i j k : Fin 3) :
    pair01 epsT i j k = (-2 / 3 : ℂ) * epsT i j k ∧ pair02 epsT i j k = (-2 / 3 : ℂ) * epsT i j k ∧
      pair01 epsT i j k + pair02 epsT i j k = (-4 / 3 : ℂ) * epsT i j k := by
  rw [pair01_eq, pair02_eq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [epsT] <;> norm_num

end Comparison

end
