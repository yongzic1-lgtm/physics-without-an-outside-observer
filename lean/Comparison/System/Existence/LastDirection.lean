import Comparison.System.Existence.Defs
import Comparison.WholePicture.Geometry
import Comparison.Existence.Pair

/-!
# The proof system, the existence layer: the last-step direction (Proposition 47)

Book IX, Prop. 47. The mass form of the division of a real line
`ℝh` (Definition 27 with the projector `hhᵀ`) is `M_h(X, Y) = 2⟨Xh, Yh⟩` for every pair of rotations, in every dimension
(`massFormLine_eq`); on `ℂ⁵ = ℝ¹⁰` it is `2 Re⟨Xh, Yh⟩` (`massFormLine_complex`). For every plane `{h, k}` the thirteen
rotations of `u(3) ⊕ u(2)` and the twelve of `s(u(3) ⊕ u(2))` are carried from the plane `{0, 1}` by a permutation of the
five directions (`moveTo`), which keeps the trace form and carries the last-step direction `e₀` to `e_h`.
-/

namespace Comparison.System.Existence

open Matrix Complex Polynomial

/-! ## The mass form of a real line -/

section MassLine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The mass form of the division of the real line `ℝh`:** `M_h(X, Y) = Tr([X, P_h]ᵀ[Y, P_h])`,
`P_h = hhᵀ` (Definition 27). -/
def massFormLine (h : ι → ℝ) (X Y : Matrix ι ι ℝ) : ℝ :=
  ((X * vecMulVec h h - vecMulVec h h * X)ᵀ * (Y * vecMulVec h h - vecMulVec h h * Y)).trace

theorem antisym_quad (X : Matrix ι ι ℝ) (hX : Xᵀ = -X) (h : ι → ℝ) : h ⬝ᵥ (X *ᵥ h) = 0 := by
  have e : h ⬝ᵥ (X *ᵥ h) = (h ᵥ* X) ⬝ᵥ h := Matrix.dotProduct_mulVec h X h
  rw [← Matrix.mulVec_transpose, hX, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm (X *ᵥ h) h] at e
  linarith

theorem comm_line_eq (h : ι → ℝ) (X : Matrix ι ι ℝ) (hX : Xᵀ = -X) :
    X * vecMulVec h h - vecMulVec h h * X = vecMulVec (X *ᵥ h) h + vecMulVec h (X *ᵥ h) := by
  have hu : h ᵥ* X = -(X *ᵥ h) := by
    rw [← Matrix.mulVec_transpose, hX, Matrix.neg_mulVec]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hu]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.neg_apply]
  ring

/-- **`M_h(X, Y) = 2⟨Xh, Yh⟩`** for rotations `X`, `Y` (antisymmetric) and a unit vector `h`. -/
theorem massFormLine_eq (h : ι → ℝ) (hh : h ⬝ᵥ h = 1) (X Y : Matrix ι ι ℝ) (hX : Xᵀ = -X) (hY : Yᵀ = -Y) :
    massFormLine h X Y = 2 * ((X *ᵥ h) ⬝ᵥ (Y *ᵥ h)) := by
  have h1 : (X *ᵥ h) ⬝ᵥ h = 0 := by rw [dotProduct_comm]; exact antisym_quad X hX h
  have h2 : h ⬝ᵥ (Y *ᵥ h) = 0 := antisym_quad Y hY h
  unfold massFormLine
  rw [comm_line_eq h X hX, comm_line_eq h Y hY, Matrix.transpose_add, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
  simp only [Matrix.trace_add, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul, hh, h1, h2]
  ring

end MassLine

/-! ## `ℂⁿ` as `ℝ²ⁿ` -/

section Realify

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex vector as a real one: its real and imaginary parts. -/
def realVec (v : n → ℂ) : n × Fin 2 → ℝ := fun p => if p.2 = 0 then (v p.1).re else (v p.1).im

/-- A complex matrix as a real one on `ℝ²ⁿ`: `[[Re X, −Im X], [Im X, Re X]]`. -/
def realify (X : Matrix n n ℂ) : Matrix (n × Fin 2) (n × Fin 2) ℝ := fun p q =>
  if p.2 = 0 then (if q.2 = 0 then (X p.1 q.1).re else -(X p.1 q.1).im)
  else (if q.2 = 0 then (X p.1 q.1).im else (X p.1 q.1).re)

theorem realVec_dot (v w : n → ℂ) : realVec v ⬝ᵥ realVec w = (star v ⬝ᵥ w).re := by
  simp only [dotProduct, realVec, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem realify_mulVec (X : Matrix n n ℂ) (v : n → ℂ) : realify X *ᵥ realVec v = realVec (X *ᵥ v) := by
  funext p
  rcases p with ⟨i, a⟩
  simp only [Matrix.mulVec, dotProduct, realify, realVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero, Complex.re_sum, Complex.mul_re]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Complex.im_sum, Complex.mul_im]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem realify_antisymm (X : Matrix n n ℂ) (hX : Xᴴ = -X) : (realify X)ᵀ = -realify X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have e := congrFun (congrFun hX j) i
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at e
  have hre : (X i j).re = -(X j i).re := by
    have := congrArg Complex.re e
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have him : (X i j).im = (X j i).im := by
    have := congrArg Complex.im e
    simp only [Complex.star_def, Complex.conj_im, Complex.neg_im] at this
    linarith
  simp only [Matrix.transpose_apply, Matrix.neg_apply, realify]
  fin_cases a <;> fin_cases b <;> simp [hre, him]

theorem realVec_unit (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) : realVec v ⬝ᵥ realVec v = 1 := by
  rw [realVec_dot, hv, Complex.one_re]

/-- **`M_h(X, Y) = 2 Re⟨Xh, Yh⟩`** on `ℂⁿ = ℝ²ⁿ`, for anti-Hermitian `X`, `Y` and a unit vector `h`. -/
theorem massFormLine_complex (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (X Y : Matrix n n ℂ) (hX : Xᴴ = -X)
    (hY : Yᴴ = -Y) :
    massFormLine (realVec v) (realify X) (realify Y) = 2 * (star (X *ᵥ v) ⬝ᵥ (Y *ᵥ v)).re := by
  rw [massFormLine_eq _ (realVec_unit v hv) _ _ (realify_antisymm X hX) (realify_antisymm Y hY),
    realify_mulVec, realify_mulVec, realVec_dot]

end Realify

/-! ## Carrying the plane `{0, 1}` to the plane `{h, k}` -/

/-- A permutation of the five directions carries a rotation: `(σX)_ab = X_{σ⁻¹a, σ⁻¹b}`. -/
def moveTo (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  X.submatrix σ.symm σ.symm

theorem moveTo_conjTranspose (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (moveTo σ X)ᴴ = moveTo σ Xᴴ := Matrix.conjTranspose_submatrix X _ _

theorem moveTo_neg (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) : moveTo σ (-X) = -moveTo σ X := rfl

theorem moveTo_mul (σ : Equiv.Perm (Fin 5)) (X Y : Matrix (Fin 5) (Fin 5) ℂ) :
    moveTo σ X * moveTo σ Y = moveTo σ (X * Y) :=
  Matrix.submatrix_mul_equiv X Y σ.symm σ.symm σ.symm

theorem moveTo_trace (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) : (moveTo σ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, moveTo, Matrix.submatrix_apply]
  exact Equiv.sum_comp σ.symm (fun i => X i i)

theorem moveTo_mulVec_single (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) (a : Fin 5) :
    moveTo σ X *ᵥ Pi.single (σ a) 1 = fun i => (X *ᵥ Pi.single a 1) (σ.symm i) := by
  funext i
  simp [moveTo, Matrix.mulVec, dotProduct, Pi.single_apply, Equiv.symm_apply_eq]

theorem dot_comp (σ : Equiv.Perm (Fin 5)) (v w : Fin 5 → ℂ) :
    star (fun i => v (σ.symm i)) ⬝ᵥ (fun i => w (σ.symm i)) = star v ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply]
  exact Equiv.sum_comp σ.symm (fun i => star (v i) * w i)

theorem perm_of_plane : ∀ h k : Fin 5, h ≠ k →
    ((Equiv.swap 0 h).trans (Equiv.swap (Equiv.swap 0 h 1) k)) 0 = h ∧
    ((Equiv.swap 0 h).trans (Equiv.swap (Equiv.swap 0 h 1) k)) 1 = k := by
  decide +kernel

theorem exists_perm (h k : Fin 5) (hk : h ≠ k) : ∃ σ : Equiv.Perm (Fin 5), σ 0 = h ∧ σ 1 = k :=
  ⟨_, perm_of_plane h k hk⟩

theorem inPlane_symm {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k) (a : Fin 5) :
    WholePicture.inPlane (σ.symm a) = decide (a ∈ ({h, k} : Finset (Fin 5))) := by
  have small : ∀ x : Fin 5, x.val < 2 ↔ x = 0 ∨ x = 1 := by decide
  have key : (σ.symm a).val < 2 ↔ a ∈ ({h, k} : Finset (Fin 5)) := by
    rw [small, Finset.mem_insert, Finset.mem_singleton, Equiv.symm_apply_eq, Equiv.symm_apply_eq, h0, h1]
  simp only [WholePicture.inPlane]
  exact decide_eq_decide.mpr key

/-! ## The thirteen rotations of `u(3) ⊕ u(2)` -/

/-- The unit `E_pq` with integer entries. -/
def eAB (p q : Fin 5) : Fin 5 → Fin 5 → ℤ := fun a b => if a = p ∧ b = q then 1 else 0

/-- The real parts of the thirteen rotations at the plane `{0, 1}` before normalization. -/
def re13 : Fin 13 → Fin 5 → Fin 5 → ℤ :=
  ![0, 0, eAB 0 1 - eAB 1 0, 0, 0, 0, 0, eAB 2 3 - eAB 3 2, eAB 2 4 - eAB 4 2, eAB 3 4 - eAB 4 3, 0, 0, 0]

/-- The imaginary parts: `iE₀₀`, `iE₁₁`, `i(E₀₁ + E₁₀)`, the three `iE_cc`, the three `i(E_cd + E_dc)`. -/
def im13 : Fin 13 → Fin 5 → Fin 5 → ℤ :=
  ![eAB 0 0, eAB 1 1, 0, eAB 0 1 + eAB 1 0, eAB 2 2, eAB 3 3, eAB 4 4, 0, 0, 0,
    eAB 2 3 + eAB 3 2, eAB 2 4 + eAB 4 2, eAB 3 4 + eAB 4 3]

/-- The squared lengths before normalization. -/
def norm13 : Fin 13 → ℕ := ![1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- The last-step direction's weights before normalization. -/
def w13Z : Fin 13 → ℤ := ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **The last-step direction's weights of the thirteen:** `1, 0, ½, ½` and nine zeros. -/
noncomputable def w13 : Fin 13 → ℝ := ![1, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **The thirteen rotations** at the plane `{0, 1}`: `(re + i im)/√n`. -/
noncomputable def turn13 (j : Fin 13) : Matrix (Fin 5) (Fin 5) ℂ :=
  (((Real.sqrt (norm13 j))⁻¹ : ℝ) : ℂ) • Matrix.of fun a b => ((re13 j a b : ℂ) + I * (im13 j a b : ℂ))

theorem re13_antisymm : ∀ (j : Fin 13) (a b : Fin 5), re13 j b a = -re13 j a b := by decide +kernel
theorem im13_symm : ∀ (j : Fin 13) (a b : Fin 5), im13 j b a = im13 j a b := by decide +kernel

theorem block13 : ∀ (j : Fin 13) (a b : Fin 5), WholePicture.inPlane a ≠ WholePicture.inPlane b →
    re13 j a b = 0 ∧ im13 j a b = 0 := by decide +kernel

theorem gram13_int : ∀ i j : Fin 13,
    ∑ a : Fin 5, ∑ b : Fin 5, (re13 i a b * re13 j a b + im13 i a b * im13 j a b) =
      if i = j then (norm13 i : ℤ) else 0 := by decide +kernel

theorem lastDirection13_int : ∀ i j : Fin 13,
    ∑ a : Fin 5, (re13 i a 0 * re13 j a 0 + im13 i a 0 * im13 j a 0) = if i = j then w13Z i else 0 := by
  decide +kernel

theorem norm13_pos (j : Fin 13) : (0 : ℝ) < norm13 j := by
  fin_cases j <;> simp [norm13]

theorem turn13_apply (j : Fin 13) (a b : Fin 5) :
    turn13 j a b = (((Real.sqrt (norm13 j))⁻¹ : ℝ) : ℂ) * ((re13 j a b : ℂ) + I * (im13 j a b : ℂ)) := by
  simp only [turn13, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

theorem turn13_re (j : Fin 13) (a b : Fin 5) :
    (turn13 j a b).re = (Real.sqrt (norm13 j))⁻¹ * re13 j a b := by
  rw [turn13_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im]
  ring

theorem turn13_im (j : Fin 13) (a b : Fin 5) :
    (turn13 j a b).im = (Real.sqrt (norm13 j))⁻¹ * im13 j a b := by
  rw [turn13_apply]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re]
  ring

theorem turn13_antiHermitian (j : Fin 13) : (turn13 j)ᴴ = -turn13 j := by
  ext a b
  have hr := re13_antisymm j a b
  have hi := im13_symm j a b
  apply Complex.ext
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_re,
      Complex.neg_re, turn13_re, hr]
    push_cast
    ring
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_im,
      Complex.neg_im, turn13_im, hi]

theorem turn13_block (j : Fin 13) (a b : Fin 5) (h : WholePicture.inPlane a ≠ WholePicture.inPlane b) :
    turn13 j a b = 0 := by
  rw [turn13_apply, (block13 j a b h).1, (block13 j a b h).2]
  simp

theorem turn13_orthonormal (i j : Fin 13) :
    ((turn13 i)ᴴ * turn13 j).trace.re = if i = j then 1 else 0 := by
  have hsum : ((turn13 i)ᴴ * turn13 j).trace.re =
      (Real.sqrt (norm13 i))⁻¹ * (Real.sqrt (norm13 j))⁻¹ *
        ∑ a : Fin 5, ∑ b : Fin 5, ((re13 i a b * re13 j a b + im13 i a b * im13 j a b : ℤ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, turn13_re, turn13_im]
    push_cast
    ring
  rw [hsum]
  simp only [← Int.cast_sum, gram13_int]
  split_ifs with h
  · subst h
    have hp := norm13_pos i
    push_cast
    rw [WholePicture.sqrt_inv_mul_self _ hp.le]
    field_simp
  · simp

theorem turn13_lastDirection (i j : Fin 13) :
    (star (turn13 i *ᵥ Pi.single 0 1) ⬝ᵥ (turn13 j *ᵥ Pi.single 0 1)).re = if i = j then w13 i else 0 := by
  have hcol : ∀ (m : Fin 13) (a : Fin 5), (turn13 m *ᵥ Pi.single 0 1) a = turn13 m a 0 := by
    intro m a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsum : (star (turn13 i *ᵥ Pi.single 0 1) ⬝ᵥ (turn13 j *ᵥ Pi.single 0 1)).re =
      (Real.sqrt (norm13 i))⁻¹ * (Real.sqrt (norm13 j))⁻¹ *
        ∑ a : Fin 5, ((re13 i a 0 * re13 j a 0 + im13 i a 0 * im13 j a 0 : ℤ) : ℝ) := by
    simp only [dotProduct, Pi.star_apply, hcol, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, turn13_re, turn13_im]
    push_cast
    ring
  rw [hsum, ← Int.cast_sum, lastDirection13_int]
  split_ifs with hij
  · subst hij
    have hp := norm13_pos i
    push_cast
    rw [WholePicture.sqrt_inv_mul_self _ hp.le]
    fin_cases i <;> norm_num [w13, w13Z, norm13]
  · simp

/-! ## Proposition 47 -/

/-- The last-step direction's line `e_h` of `ℂ⁵`. -/
def lastDirectionAt (h : Fin 5) : Fin 5 → ℂ := Pi.single h 1

/-- **Proposition 47 (the last-step direction), without the spanning** (`LastDirectionUnit.lean`: `prop_47`). The mass form of the division of the real line `ℝh` is `M_h(X, Y) = 2⟨Xh, Yh⟩`
for rotations of any real space and a unit vector `h`, so on `ℂ⁵ = ℝ¹⁰` `M_h(X, X) = 2|Xh|²` for every anti-Hermitian
`X`; for every plane `{h, k}` there are thirteen rotations that keep the plane and its outside (no entry across), orthonormal
for `Re tr(X†Y)`, on which `½M_h(X_i, X_j) = Re⟨X_ih, X_jh⟩ = diag(1, 0, ½, ½, 0, …, 0)`: three of the thirteen move
the last-step direction, `w_h = 3/13`, `χ_h = w_h(1 − w_h) = 30/169`; and twelve such rotations of trace zero, orthonormal, on which the
form has `det(x − G) = x⁹(x − ½)²(x − 4/5)`: `½M_h = 4/5, ½, ½, 0⁹`; `(½)/(4/5) = 5/8`, `sin²θ = 1 − 5/8 = 3/8`.

Recognition: the last-step direction moves `W⁺`, `W⁻` and `Z` (Gram eigenvalues `½, ½, 4/5`); nine stay massless, the photon and the
eight colour rotations; the last-step direction's length is the Higgs scalar; at the source `M_W²/M_Z² = 5/8`, `sin²θ_W = 3/8`. Uses
Props. 21, 39, 46, Definition 27. -/
theorem prop_47_core :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (X Y : Matrix ι ι ℝ), h ⬝ᵥ h = 1 → Xᵀ = -X →
      Yᵀ = -Y → massFormLine h X Y = 2 * ((X *ᵥ h) ⬝ᵥ (Y *ᵥ h))) ∧
    (∀ (v : Fin 5 → ℂ) (X : Matrix (Fin 5) (Fin 5) ℂ), star v ⬝ᵥ v = 1 → Xᴴ = -X →
      massFormLine (realVec v) (realify X) (realify X) = 2 * (star (X *ᵥ v) ⬝ᵥ (X *ᵥ v)).re) ∧
    (∀ h k : Fin 5, h ≠ k → ∃ T : Fin 13 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, (T j)ᴴ = -T j) ∧
      (∀ j a b, (a ∈ ({h, k} : Finset (Fin 5)) ↔ b ∉ ({h, k} : Finset (Fin 5))) → T j a b = 0) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (∀ i j, (star (T i *ᵥ lastDirectionAt h) ⬝ᵥ (T j *ᵥ lastDirectionAt h)).re = if i = j then w13 i else 0)) ∧
    ((Finset.univ.filter fun j => w13Z j ≠ 0).card = 3 ∧ (∀ j, w13 j = (w13Z j : ℝ) / norm13 j) ∧
      (3 : ℚ) / 13 * (1 - 3 / 13) = 30 / 169) ∧
    (∀ h k : Fin 5, h ≠ k → ∃ T : Fin 12 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, (T j)ᴴ = -T j) ∧ (∀ j, (T j).trace = 0) ∧
      (∀ j a b, (a ∈ ({h, k} : Finset (Fin 5)) ↔ b ∉ ({h, k} : Finset (Fin 5))) → T j a b = 0) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (Matrix.of fun i j => (star (T i *ᵥ lastDirectionAt h) ⬝ᵥ (T j *ᵥ lastDirectionAt h)).re).charpoly =
        X ^ 9 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ))) ∧
    ((1 / 2 : ℝ) / (4 / 5) = 5 / 8 ∧ 1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8) := by
  have hblock : ∀ {σ : Equiv.Perm (Fin 5)} {h k : Fin 5}, σ 0 = h → σ 1 = k → ∀ a b : Fin 5,
      (a ∈ ({h, k} : Finset (Fin 5)) ↔ b ∉ ({h, k} : Finset (Fin 5))) →
        WholePicture.inPlane (σ.symm a) ≠ WholePicture.inPlane (σ.symm b) := by
    intro σ h k h0 h1 a b hab
    rw [inPlane_symm h0 h1, inPlane_symm h0 h1]
    by_cases ha : a ∈ ({h, k} : Finset (Fin 5))
    · have hb := hab.mp ha
      simp [ha, hb]
    · have hb : b ∈ ({h, k} : Finset (Fin 5)) := by
        by_contra hb
        exact ha (hab.mpr hb)
      simp [ha, hb]
  have hhand : ∀ {σ : Equiv.Perm (Fin 5)} {h : Fin 5}, σ 0 = h → ∀ X Y : Matrix (Fin 5) (Fin 5) ℂ,
      star (moveTo σ X *ᵥ lastDirectionAt h) ⬝ᵥ (moveTo σ Y *ᵥ lastDirectionAt h) =
        star (X *ᵥ Pi.single 0 1) ⬝ᵥ (Y *ᵥ Pi.single 0 1) := by
    intro σ h h0 X Y
    rw [lastDirectionAt, ← h0, moveTo_mulVec_single, moveTo_mulVec_single, dot_comp]
  have horth : ∀ (σ : Equiv.Perm (Fin 5)) (X Y : Matrix (Fin 5) (Fin 5) ℂ),
      ((moveTo σ X)ᴴ * moveTo σ Y).trace = (Xᴴ * Y).trace := by
    intro σ X Y
    rw [moveTo_conjTranspose, moveTo_mul, moveTo_trace]
  refine ⟨fun ι _ _ h X Y hh hX hY => massFormLine_eq h hh X Y hX hY,
    fun v X hv hX => massFormLine_complex v hv X X hX hX, fun h k hk => ?_,
    ⟨by decide, fun j => by fin_cases j <;> norm_num [w13, w13Z, norm13], by norm_num⟩,
    fun h k hk => ?_, WholePicture.source_ratios⟩
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    refine ⟨fun j => moveTo σ (turn13 j), fun j => ?_, fun j a b hab => ?_, fun i j => ?_, fun i j => ?_⟩
    · dsimp only
      rw [moveTo_conjTranspose, turn13_antiHermitian, moveTo_neg]
    · exact turn13_block j _ _ (hblock h0 h1 a b hab)
    · dsimp only
      rw [horth, turn13_orthonormal]
    · dsimp only
      rw [hhand h0, turn13_lastDirection]
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    refine ⟨fun j => moveTo σ (WholePicture.gen12 j), fun j => ?_, fun j => ?_, fun j a b hab => ?_,
      fun i j => ?_, ?_⟩
    · dsimp only
      rw [moveTo_conjTranspose, WholePicture.gen12_antiHermitian, moveTo_neg]
    · dsimp only
      rw [moveTo_trace, WholePicture.gen12_trace]
    · exact WholePicture.gen12_block j _ _ (hblock h0 h1 a b hab)
    · dsimp only
      rw [horth, WholePicture.gen12_orthonormal]
    · have hG : (Matrix.of fun i j => (star (moveTo σ (WholePicture.gen12 i) *ᵥ lastDirectionAt h) ⬝ᵥ
          (moveTo σ (WholePicture.gen12 j) *ᵥ lastDirectionAt h)).re) = WholePicture.lastDirectionGram := by
        ext i j
        rw [Matrix.of_apply, hhand h0]
        rfl
      rw [hG, WholePicture.lastDirectionGram_charpoly]

end Comparison.System.Existence
