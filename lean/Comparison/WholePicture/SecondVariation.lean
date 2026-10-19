module

public import Comparison.Existence.PlaquetteData

/-!
# The whole picture, statement 15: the exact second variation at every complex step

`Plaquette.lean` proves
`S₂ = −(u⁴/Δ²)‖Cθ‖²` for real `u`, `a` (`S2_eq`, `kappa_eq`). Here the same is proved entry by entry
and for every complex `w`, as the Hessian of `log det(I − wA₋[e^{iθ}])` at `θ = 0` in the forty link
phases: with `A(θ)_{VU} = A_{VU}e^{iθ_ℓ}`, `A(θ)_{UV} = A_{UV}e^{−iθ_ℓ}` on the link `ℓ = (U, V)`,
its first and second phase derivatives are `dA ℓ` and `d2A ℓ`, the resolvent is
`R = (I − wA)⁻¹ = (I + wA)/(1 − 5w²)` (`resolventW_spec`, since `A² = 5`), and

  `H_{ℓm}(w) = −w² tr(R ∂_ℓA R ∂_mA) − δ_{ℓm} w tr(R ∂²_ℓA)`.

* `hessLaw_eq`: **`H(w) = −κ(w) CᵀC`, `κ(w) = 2w⁴/(1 − 5w²)²`**, for every complex `w` with
  `1 − 5w² ≠ 0`: an identity of rational functions of `w`.
* `kappa_quarters`: `κ = 1/200` at the counting points `w = ±1/5` and `1/98` at the amplitude
  points `w = ±i/3`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Complex

/-- The sign of the signed step on the link `ℓ`: `s_ℓ = A_{UV}`. -/
def linkSign (l : Fin 40) : ℤ := sadjZ (linkU l) (linkV l)

theorem linkSign_sq : ∀ l : Fin 40, linkSign l * linkSign l = 1 := by decide

theorem sadjZ_VU : ∀ l : Fin 40, sadjZ (linkV l) (linkU l) = linkSign l := by decide

/-- The signed step over `ℂ`. -/
noncomputable def AC : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of fun x y => (sadjZ x y : ℂ)

theorem AC_sq : AC * AC = (5 : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  ext x y
  have h := congrFun (congrFun sadjZ_sq x) y
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have h' := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at h'
  simp only [Matrix.mul_apply, AC, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [h']

/-- The link `ℓ` as a rotation from `U` to `V`: `X_ℓ = E_{VU} − E_{UV}`. -/
noncomputable def linkX (l : Fin 40) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.single (linkV l) (linkU l) 1 - Matrix.single (linkU l) (linkV l) 1

/-- **`∂A₋[e^{iθ}]/∂θ_ℓ` at `θ = 0`:** `i s_ℓ X_ℓ`. -/
noncomputable def dA (l : Fin 40) : Matrix (Fin 16) (Fin 16) ℂ := (I * (linkSign l : ℂ)) • linkX l

/-- **`∂²A₋[e^{iθ}]/∂θ_ℓ²` at `θ = 0`:** `−s_ℓ(E_{VU} + E_{UV})`. -/
noncomputable def d2A (l : Fin 40) : Matrix (Fin 16) (Fin 16) ℂ :=
  (-(linkSign l : ℂ)) • (Matrix.single (linkV l) (linkU l) 1 + Matrix.single (linkU l) (linkV l) 1)

/-- **The resolvent** `R = (I + wA)/(1 − 5w²)`. -/
noncomputable def resolventW (w : ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  (1 - 5 * w ^ 2)⁻¹ • (1 + w • AC)

/-- `(I − wA) R = I`: the resolvent is `(I − wA)⁻¹`. -/
theorem resolventW_spec (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) :
    (1 - w • AC) * resolventW w = 1 := by
  have h : (1 - w • AC) * (1 + w • AC) = (1 - 5 * w ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, AC_sq, smul_smul]
    module
  rw [resolventW, Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hw, one_smul]

/-- **The Hessian of the signed law** in the link phases at `θ = 0`. -/
noncomputable def hessLaw (w : ℂ) (j k : Fin 40) : ℂ :=
  -(w ^ 2 * (resolventW w * dA j * resolventW w * dA k).trace) -
    (if j = k then w * (resolventW w * d2A j).trace else 0)

/-! ## Traces against single entries -/

theorem trace_single_single (a b c d : Fin 16) :
    (Matrix.single a b (1 : ℂ) * Matrix.single c d 1).trace = if b = c ∧ a = d then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : b = c <;> by_cases h2 : a = d <;> simp [h1, h2, Finset.sum_ite_eq,
    ite_and]

theorem trace_M_single_single (M : Matrix (Fin 16) (Fin 16) ℂ) (a b c d : Fin 16) :
    (M * Matrix.single a b 1 * Matrix.single c d 1).trace = if b = c then M d a else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : b = c <;> simp [h1, Finset.sum_ite_eq, ite_and, mul_ite]


theorem trace_M_single_M_single (M : Matrix (Fin 16) (Fin 16) ℂ) (a b c d : Fin 16) :
    (M * Matrix.single a b 1 * M * Matrix.single c d 1).trace = M d a * M b c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one,
    mul_zero]
  simp [Finset.sum_ite_eq, ite_and]

theorem trace_M_single (M : Matrix (Fin 16) (Fin 16) ℂ) (a b : Fin 16) :
    (M * Matrix.single a b 1).trace = M b a := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp [Finset.sum_ite_eq]

/-! ## The finite facts of the links -/

/-- `tr(X_jX_k) = −2δ_{jk}`. -/
theorem linkX_pair : ∀ j k : Fin 40,
    ((if linkU j = linkV k ∧ linkV j = linkU k then 1 else 0) -
      (if linkU j = linkU k ∧ linkV j = linkV k then 1 else 0) -
      (if linkV j = linkV k ∧ linkU j = linkU k then 1 else 0) +
      (if linkV j = linkU k ∧ linkU j = linkV k then 1 else 0) : ℤ) =
      if j = k then -2 else 0 := by decide +kernel

/-- **No triangles:** `tr(A X_j X_k) = 0`. -/
theorem linkX_triangle : ∀ j k : Fin 40,
    ((if linkU j = linkV k then sadjZ (linkU k) (linkV j) else 0) -
      (if linkU j = linkU k then sadjZ (linkV k) (linkV j) else 0) -
      (if linkV j = linkV k then sadjZ (linkU k) (linkU j) else 0) +
      (if linkV j = linkU k then sadjZ (linkV k) (linkU j) else 0) : ℤ) = 0 := by decide +kernel

theorem trace_linkX_linkX (j k : Fin 40) :
    (linkX j * linkX k).trace = if j = k then -2 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (linkX_pair j k)
  push_cast at h
  simp only [linkX, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, trace_single_single]
  rw [← h]
  ring

theorem trace_AC_linkX_linkX (j k : Fin 40) : (AC * linkX j * linkX k).trace = 0 := by
  simp only [linkX, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, trace_M_single_single, AC,
    Matrix.of_apply]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (linkX_triangle j k)
  push_cast at h
  linear_combination h

theorem trace_linkX_AC_linkX (j k : Fin 40) : (linkX j * AC * linkX k).trace = 0 := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, trace_AC_linkX_linkX]

/-- `s_j s_k tr(AX_jAX_k) = B₄(j, k) = 10δ_{jk} − 2(CᵀC)_{jk}` (`B4Z_eq`). -/
theorem trace_AC_linkX_AC_linkX (j k : Fin 40) :
    (linkSign j * linkSign k : ℂ) * (AC * linkX j * AC * linkX k).trace =
      10 * (if j = k then 1 else 0) - 2 * (GZ j k : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (B4Z_eq j k)
  push_cast at h
  rw [← h]
  simp only [linkX, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    trace_M_single_M_single, AC, Matrix.of_apply, B4Z, linkSign]
  push_cast
  ring

theorem trace_single_ne {a b : Fin 16} (h : a ≠ b) : (Matrix.single a b (1 : ℂ)).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.single_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  exact absurd (h1.trans h2.symm) h

theorem trace_d2A (j : Fin 40) : (d2A j).trace = 0 := by
  have hne : linkV j ≠ linkU j := (links_ok j).1.ne'
  rw [d2A, Matrix.trace_smul, Matrix.trace_add, trace_single_ne hne, trace_single_ne hne.symm]
  simp

theorem trace_AC_d2A (j : Fin 40) : (AC * d2A j).trace = -2 := by
  have hs := congrArg (fun z : ℤ => (z : ℂ)) (linkSign_sq j)
  have hv := congrArg (fun z : ℤ => (z : ℂ)) (sadjZ_VU j)
  push_cast at hs hv
  simp only [d2A, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    trace_M_single, AC, Matrix.of_apply, smul_eq_mul]
  rw [hv]
  simp only [linkSign] at hs ⊢
  linear_combination (-2 : ℂ) * hs

/-! ## The second variation -/

/-- **The exact second variation of the signed law in the forty link phases:**
`H(w) = −κ(w) CᵀC` with `κ(w) = 2w⁴/(1 − 5w²)²`, for every complex `w` with `1 − 5w² ≠ 0`. -/
theorem hessLaw_eq (w : ℂ) (_hw : 1 - 5 * w ^ 2 ≠ 0) (j k : Fin 40) :
    hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ) := by
  have hsand : ∀ (M Y Z : Matrix (Fin 16) (Fin 16) ℂ),
      ((1 + w • M) * Y * (1 + w • M) * Z).trace =
        (Y * Z).trace + w * (M * Y * Z).trace + w * (Y * M * Z).trace +
          w ^ 2 * (M * Y * M * Z).trace := by
    intro M Y Z
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  have hRR : (resolventW w * dA j * resolventW w * dA k).trace =
      ((1 - 5 * w ^ 2)⁻¹) ^ 2 * (I * I) * ((linkSign j * linkSign k : ℂ) *
        ((linkX j * linkX k).trace + w * (AC * linkX j * linkX k).trace +
          w * (linkX j * AC * linkX k).trace + w ^ 2 * (AC * linkX j * AC * linkX k).trace)) := by
    have e : resolventW w * dA j * resolventW w * dA k =
        (((1 - 5 * w ^ 2)⁻¹) ^ 2 * (I * I) * (linkSign j * linkSign k : ℂ)) •
          ((1 + w • AC) * linkX j * (1 + w • AC) * linkX k) := by
      simp only [resolventW, dA, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
    rw [e, Matrix.trace_smul, hsand, smul_eq_mul]
    ring
  have hR2 : (resolventW w * d2A j).trace =
      (1 - 5 * w ^ 2)⁻¹ * ((d2A j).trace + w * (AC * d2A j).trace) := by
    simp only [resolventW, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul]
  have hX := trace_linkX_linkX j k
  have hA := trace_AC_linkX_AC_linkX j k
  rw [hessLaw, hRR, hR2, trace_AC_linkX_linkX, trace_linkX_AC_linkX, trace_d2A, trace_AC_d2A]
  by_cases hjk : j = k
  · subst hjk
    have hs := congrArg (fun z : ℤ => (z : ℂ)) (linkSign_sq j)
    push_cast at hs
    simp only [ite_true] at hX hA ⊢
    rw [hX]
    have e : (linkSign j * linkSign j : ℂ) * (-2 + w * 0 + w * 0 +
        w ^ 2 * (AC * linkX j * AC * linkX j).trace) =
        -2 * (linkSign j * linkSign j : ℂ) + w ^ 2 * (10 * 1 - 2 * (GZ j j : ℂ)) := by
      rw [← hA]
      ring
    rw [e, hs, I_mul_I]
    field_simp
    ring
  · simp only [hjk, ite_false] at hX hA ⊢
    rw [hX]
    have e : (linkSign j * linkSign k : ℂ) * (0 + w * 0 + w * 0 +
        w ^ 2 * (AC * linkX j * AC * linkX k).trace) = w ^ 2 * (10 * 0 - 2 * (GZ j k : ℂ)) := by
      rw [← hA]
      ring
    rw [e, I_mul_I]
    field_simp
    ring

/-- **`κ(w) = 2w⁴/(1 − 5w²)²` at the four points `u = i^d/4`:** `1/200` at `w = ±1/5` (the counting points
`u = ±1/4`) and `1/98` at `w = ±i/3` (the amplitude points `u = ±i/4`), `w = u/(1 + 4u²)`. -/
theorem kappa_quarters :
    (1 / 4 : ℂ) / (1 + 4 * (1 / 4) ^ 2) = 1 / 5 ∧ (-1 / 4 : ℂ) / (1 + 4 * (-1 / 4) ^ 2) = -1 / 5 ∧
    (I / 4) / (1 + 4 * (I / 4) ^ 2) = I / 3 ∧ (-I / 4) / (1 + 4 * (-I / 4) ^ 2) = -I / 3 ∧
    2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
    2 * (-1 / 5 : ℂ) ^ 4 / (1 - 5 * (-1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
    2 * (I / 3) ^ 4 / (1 - 5 * (I / 3) ^ 2) ^ 2 = 1 / 98 ∧
    2 * (-I / 3) ^ 4 / (1 - 5 * (-I / 3) ^ 2) ^ 2 = 1 / 98 := by
  have h2 : I ^ 2 = -1 := I_sq
  have q1 : (I / 4) ^ 2 = -1 / 16 := by rw [div_pow, h2]; norm_num
  have q2 : (-I / 4) ^ 2 = -1 / 16 := by rw [div_pow, neg_sq, h2]; norm_num
  have q3 : (I / 3) ^ 2 = -1 / 9 := by rw [div_pow, h2]; norm_num
  have q4 : (-I / 3) ^ 2 = -1 / 9 := by rw [div_pow, neg_sq, h2]; norm_num
  have q5 : (I / 3) ^ 4 = 1 / 81 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, q3]; norm_num
  have q6 : (-I / 3) ^ 4 = 1 / 81 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, q4]; norm_num
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · rw [q1]
    ring
  · rw [q2]
    ring
  · rw [q5, q3]
    norm_num
  · rw [q6, q4]
    norm_num

end Comparison.WholePicture

end
