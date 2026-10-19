module

public import Comparison.Existence.PlaquetteData
public import Comparison.Existence.CovDiff

/-!
# Book XI. The law in small phases: the second variation (Proposition 62)

The finite data are in
`PlaquetteData.lean`. U(1) phases `θ` sit on the forty links: `phaseMat θ = Σ_ℓ θ_ℓ (E_uv − E_vu)`,
the antisymmetric `Θ`. With `A = sadj` the signed step (`A² = 5`):

* `circ θ q`: the phases summed around the square `q`, the entries of `Cθ`; `circ_eq`: linear in `θ`;
  `plaqSq θ = ‖Cθ‖²`; `circ_grad`: **`C · grad = 0`**.
* `Hm θ = A∘Θ` (so that `A₁ = iHm`), `Wm θ = A∘Θ∘Θ` (so that `A₂ = −½Wm`).
* `T4_eq`: **`tr(A Hm A Hm) = 10 Σθ² − 2‖Cθ‖²`** for every `θ`, from `B4Z_eq`; with the `i²` of the
  two `A₁` this is the book's `T₄ = tr(A₋A₁A₋A₁) = 2‖Cθ‖² − 10Σθ²`.
* `trace_AW`, `trace_HH`, `trace_W`, `trace_AHH`: `tr(AW) = 2Σθ²`, `tr(H²) = −2Σθ²`, `tr W = 0`,
  `tr(AH²) = 0` (no triangles).
* `Kinv_spec`: `(a − uA)(a + uA)/Δ = 1`, `Δ = a² − 5u²`.
* `S2 u a θ = −u tr(K⁻¹A₂) − (u²/2) tr(K⁻¹A₁K⁻¹A₁)`; `S2_eq`: **`S₂ = −(u⁴/Δ²)‖Cθ‖²`** for every
  `θ`, the gradient part included: the `Σθ²` terms cancel because `Δ = a² − 5u²`.
* `kappa_eq`, `kappa_quarter`: `u⁴/Δ² = κ(w)/2`, `κ(w) = 2w⁴/(1 − 5w²)²`, `w = u/(1 + 4u²)`, and
  **`κ(1/4) = 1/200`**.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex

/-! ## The real objects -/

/-- `A` over the reals. -/
noncomputable def sadj : Matrix (Fin 16) (Fin 16) ℝ := sadjZ.map (Int.castRingHom ℝ)

theorem sadj_apply (x y : Fin 16) : sadj x y = (sadjZ x y : ℝ) := rfl

theorem sadj_symm (x y : Fin 16) : sadj x y = sadj y x := by
  rw [sadj_apply, sadj_apply, sadjZ_symm]

/-- **`A² = 5`.** -/
theorem sadj_sq : sadj * sadj = (5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  rw [sadj, ← Matrix.map_mul, sadjZ_sq]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The link `ℓ` over the reals. -/
noncomputable def linkM (l : Fin 40) : Matrix (Fin 16) (Fin 16) ℝ := (linkZ l).map (Int.castRingHom ℝ)

theorem linkM_apply (l : Fin 40) (x y : Fin 16) : linkM l x y = (linkZ l x y : ℝ) := rfl

/-- **The phases on the forty links:** `Θ = Σ_ℓ θ_ℓ (E_uv − E_vu)`. -/
noncomputable def phaseMat (θ : Fin 40 → ℝ) : Matrix (Fin 16) (Fin 16) ℝ := ∑ l, θ l • linkM l

theorem phaseMat_apply (θ : Fin 40 → ℝ) (x y : Fin 16) :
    phaseMat θ x y = ∑ l, θ l * (linkZ l x y : ℝ) := by
  simp [phaseMat, Matrix.sum_apply, linkM_apply]

theorem linkZ_antisymm (l : Fin 40) (x y : Fin 16) : linkZ l y x = -linkZ l x y := by
  have h := (links_ok l).1
  simp only [linkZ, Matrix.of_apply]
  by_cases h1 : x = linkU l ∧ y = linkV l
  · obtain ⟨rfl, rfl⟩ := h1
    simp [h.ne', h.ne]
  · by_cases h2 : x = linkV l ∧ y = linkU l
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h.ne', h.ne]
    · rw [if_neg (fun h' => h2 ⟨h'.2, h'.1⟩), if_neg (fun h' => h1 ⟨h'.2, h'.1⟩), if_neg h1,
        if_neg h2, neg_zero]

theorem phaseMat_antisymm (θ : Fin 40 → ℝ) (x y : Fin 16) : phaseMat θ y x = -phaseMat θ x y := by
  rw [phaseMat_apply, phaseMat_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [linkZ_antisymm]
  push_cast
  ring

/-! ## The squares -/

/-- The phases summed around the square `q`: the entry `(Cθ)_q`. -/
noncomputable def circ (θ : Fin 40 → ℝ) (q : Fin 40) : ℝ :=
  phaseMat θ (sqVert q 1) (sqVert q 0) + phaseMat θ (sqVert q 2) (sqVert q 1) +
    phaseMat θ (sqVert q 3) (sqVert q 2) + phaseMat θ (sqVert q 0) (sqVert q 3)

theorem circ_eq (θ : Fin 40 → ℝ) (q : Fin 40) : circ θ q = ∑ l, θ l * (cZ q l : ℝ) := by
  simp only [circ, phaseMat_apply, ← Finset.sum_add_distrib, cZ]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring

/-- `‖Cθ‖² = Σ_q (Cθ)_q²`. -/
noncomputable def plaqSq (θ : Fin 40 → ℝ) : ℝ := ∑ q, circ θ q ^ 2

/-- `Σθ²`. -/
noncomputable def linkSq (θ : Fin 40 → ℝ) : ℝ := ∑ l, θ l ^ 2

theorem plaqSq_eq (θ : Fin 40 → ℝ) : plaqSq θ = ∑ l, ∑ m, θ l * θ m * (GZ l m : ℝ) := by
  simp only [plaqSq, circ_eq, pow_two, Finset.sum_mul_sum, GZ]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **`C · grad = 0`:** a gradient of phases sums to zero around every square. -/
theorem circ_grad (φ : Fin 16 → ℝ) (q : Fin 40) :
    circ (fun l => φ (linkV l) - φ (linkU l)) q = 0 := by
  rw [circ_eq]
  have h : ∀ l : Fin 40, (φ (linkV l) - φ (linkU l)) * (cZ q l : ℝ) =
      ∑ x, φ x * ((cZ q l : ℝ) * ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0))) := by
    intro l
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← Finset.mul_sum]
  have hz := cZ_div q x
  have : ∑ l : Fin 40, (cZ q l : ℝ) * ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)) =
      ((∑ l : Fin 40, cZ q l * ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [this, hz, Int.cast_zero, mul_zero]

/-! ## The four-step closed walks -/

/-- `A₁/i = A∘Θ`. -/
noncomputable def Hm (θ : Fin 40 → ℝ) : Matrix (Fin 16) (Fin 16) ℝ := Matrix.hadamard sadj (phaseMat θ)

/-- `−2A₂ = A∘Θ∘Θ`. -/
noncomputable def Wm (θ : Fin 40 → ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.hadamard sadj (Matrix.hadamard (phaseMat θ) (phaseMat θ))

theorem linkM_eq (l : Fin 40) :
    linkM l = Matrix.single (linkU l) (linkV l) 1 - Matrix.single (linkV l) (linkU l) 1 := by
  have h := (links_ok l).1
  ext x y
  simp only [linkM_apply, linkZ, Matrix.of_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases h1 : x = linkU l ∧ y = linkV l
  · obtain ⟨rfl, rfl⟩ := h1
    simp [h.ne']
  · by_cases h2 : x = linkV l ∧ y = linkU l
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h.ne']
    · have h1' : ¬(linkU l = x ∧ linkV l = y) := fun h' => h1 ⟨h'.1.symm, h'.2.symm⟩
      have h2' : ¬(linkV l = x ∧ linkU l = y) := fun h' => h2 ⟨h'.1.symm, h'.2.symm⟩
      simp [h1, h2, h1', h2']

theorem hadamard_linkM (l : Fin 40) :
    Matrix.hadamard sadj (linkM l) = sadj (linkU l) (linkV l) • linkM l := by
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.smul_apply, smul_eq_mul, linkM_apply, linkZ,
    Matrix.of_apply]
  by_cases h1 : x = linkU l ∧ y = linkV l
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : x = linkV l ∧ y = linkU l
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1, sadj_symm]
    · simp [h1, h2]

theorem Hm_eq (θ : Fin 40 → ℝ) :
    Hm θ = ∑ l, (θ l * sadj (linkU l) (linkV l)) • linkM l := by
  rw [Hm, phaseMat]
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrFun (congrFun (hadamard_linkM l) x) y
  simp only [Matrix.hadamard_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [mul_left_comm, this]
  ring

theorem trace4_single (A : Matrix (Fin 16) (Fin 16) ℝ) (a b c d : Fin 16) :
    (A * Matrix.single a b 1 * A * Matrix.single c d 1).trace = A d a * A b c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, one_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

theorem trace_linkM (A : Matrix (Fin 16) (Fin 16) ℝ) (l m : Fin 40) :
    (A * linkM l * A * linkM m).trace =
      A (linkV m) (linkU l) * A (linkV l) (linkU m) - A (linkU m) (linkU l) * A (linkV l) (linkV m) -
        A (linkV m) (linkV l) * A (linkU l) (linkU m) + A (linkU m) (linkV l) * A (linkU l) (linkV m) := by
  rw [linkM_eq, linkM_eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, trace4_single]
  ring

theorem trace_quad (G G' : Matrix (Fin 16) (Fin 16) ℝ) (x y : Fin 40 → ℝ)
    (M N : Fin 40 → Matrix (Fin 16) (Fin 16) ℝ) :
    (G * (∑ l, x l • M l) * G' * (∑ m, y m • N m)).trace =
      ∑ l, ∑ m, x l * y m * (G * M l * G' * N m).trace := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **`tr(A(A∘Θ)A(A∘Θ)) = Σ_{ℓ,m} θ_ℓθ_m B₄(ℓ, m)`.** -/
theorem T4_expand (θ : Fin 40 → ℝ) :
    (sadj * Hm θ * sadj * Hm θ).trace = ∑ l, ∑ m, θ l * θ m * (B4Z l m : ℝ) := by
  rw [Hm_eq, trace_quad]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [trace_linkM]
  simp only [B4Z, sadj_apply]
  push_cast
  ring

/-- **The four-step closed walks against the squares:** `tr(A Hm A Hm) = 10Σθ² − 2‖Cθ‖²`. -/
theorem T4_eq (θ : Fin 40 → ℝ) :
    (sadj * Hm θ * sadj * Hm θ).trace = 10 * linkSq θ - 2 * plaqSq θ := by
  rw [T4_expand, plaqSq_eq, linkSq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl : θ l ^ 2 = ∑ m, θ l * θ m * (if l = m then 1 else 0) := by
    rw [Finset.sum_eq_single l]
    · simp [pow_two]
    · intro m _ hm
      simp [Ne.symm hm]
    · simp
  rw [hl, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [B4Z_eq]
  push_cast
  split_ifs <;> ring

/-! ## The shorter walks -/

theorem phase_sq_expand (θ : Fin 40 → ℝ) :
    ∑ x, ∑ y, sadj x y * sadj x y * phaseMat θ x y * phaseMat θ x y = 2 * linkSq θ := by
  set F : Fin 16 → Fin 16 → Fin 40 → Fin 40 → ℝ := fun x y l m =>
    θ l * θ m * ((sadjZ x y * sadjZ x y * linkZ l x y * linkZ m x y : ℤ) : ℝ) with hF
  have key : ∀ x y, sadj x y * sadj x y * phaseMat θ x y * phaseMat θ x y = ∑ l, ∑ m, F x y l m := by
    intro x y
    rw [phaseMat_apply, sadj_apply, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hF]
    push_cast
    ring
  simp only [key]
  calc ∑ x, ∑ y, ∑ l, ∑ m, F x y l m = ∑ x, ∑ l, ∑ y, ∑ m, F x y l m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ l, ∑ m, ∑ y, F x y l m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l, ∑ x, ∑ m, ∑ y, F x y l m := Finset.sum_comm
    _ = ∑ l, ∑ m, ∑ x, ∑ y, F x y l m := Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l, ∑ m, θ l * θ m * (2 * (if l = m then 1 else 0)) := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        simp only [hF, ← Finset.mul_sum]
        congr 1
        have := NZ_eq l m
        exact_mod_cast this
    _ = 2 * linkSq θ := by
        rw [linkSq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single l]
        · simp [pow_two]
          ring
        · intro m _ hm
          simp [Ne.symm hm]
        · simp

/-- `tr(A W) = 2Σθ²`. -/
theorem trace_AW (θ : Fin 40 → ℝ) : (sadj * Wm θ).trace = 2 * linkSq θ := by
  rw [← phase_sq_expand]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Wm, Matrix.hadamard_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [sadj_symm y x, phaseMat_antisymm θ x y]
  ring

/-- `tr(H²) = −2Σθ²`. -/
theorem trace_HH (θ : Fin 40 → ℝ) : (Hm θ * Hm θ).trace = -(2 * linkSq θ) := by
  rw [← phase_sq_expand, ← Finset.sum_neg_distrib]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Hm, Matrix.hadamard_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sadj_symm y x, phaseMat_antisymm θ x y]
  ring

/-- `tr W = 0`. -/
theorem trace_W (θ : Fin 40 → ℝ) : (Wm θ).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Wm, Matrix.hadamard_apply, sadj_apply, sadjZ_diag,
    Int.cast_zero, zero_mul, Finset.sum_const_zero]

/-- `tr(AH²) = 0`: there are no triangles. -/
theorem trace_AHH (θ : Fin 40 → ℝ) : (sadj * Hm θ * Hm θ).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Hm, Matrix.hadamard_apply,
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun y _ => ?_
  have h := sadjZ_tri x y z
  have h' : sadj x y * sadj y z * sadj z x = 0 := by
    rw [sadj_apply, sadj_apply, sadj_apply]
    exact_mod_cast h
  calc sadj x y * (sadj y z * phaseMat θ y z) * (sadj z x * phaseMat θ z x)
      = (sadj x y * sadj y z * sadj z x) * (phaseMat θ y z * phaseMat θ z x) := by ring
    _ = 0 := by rw [h', zero_mul]

theorem trace_HAH (θ : Fin 40 → ℝ) : (Hm θ * sadj * Hm θ).trace = 0 := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    trace_AHH]

/-! ## The second variation -/

/-- `(a − uA)(a + uA)/Δ = 1`: the inverse of `K = a − uA` is `(a + uA)/Δ`, `Δ = a² − 5u²`. -/
theorem Kinv_spec (u a : ℝ) (hΔ : a ^ 2 - 5 * u ^ 2 ≠ 0) :
    (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) - u • sadj) *
      ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) = 1 := by
  have h : (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) - u • sadj) * (a • 1 + u • sadj) =
      (a ^ 2 - 5 * u ^ 2) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, sadj_sq, smul_smul]
    module
  rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hΔ, one_smul]

theorem trace_toC (X : Matrix (Fin 16) (Fin 16) ℝ) : (toC X).trace = ((X.trace : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, toC_apply, Complex.ofReal_sum]

/-- **The second-order part of the signed law** in the phases:
`S₂ = −u tr(K⁻¹A₂) − (u²/2) tr(K⁻¹A₁K⁻¹A₁)`, `K⁻¹ = (a + uA)/Δ`, `A₁ = i(A∘Θ)`, `A₂ = −½A∘Θ∘Θ`. -/
noncomputable def S2 (u a : ℝ) (θ : Fin 40 → ℝ) : ℂ :=
  -(u : ℂ) * (toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) *
      (((-1 / 2 : ℝ) : ℂ) • toC (Wm θ))).trace -
    (u : ℂ) ^ 2 / 2 * (toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * (I • toC (Hm θ)) *
      toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * (I • toC (Hm θ))).trace

theorem trace_KW (u a : ℝ) (θ : Fin 40 → ℝ) :
    (((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) + u • sadj)) * Wm θ).trace =
      (a ^ 2 - 5 * u ^ 2)⁻¹ * (u * (2 * linkSq θ)) := by
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add,
    trace_W, trace_AW, smul_eq_mul]
  ring

theorem trace_KHKH (u a : ℝ) (θ : Fin 40 → ℝ) :
    (((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) + u • sadj)) * Hm θ *
        ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * Hm θ).trace =
      ((a ^ 2 - 5 * u ^ 2)⁻¹) ^ 2 * (a ^ 2 * (-(2 * linkSq θ)) +
        u ^ 2 * (10 * linkSq θ - 2 * plaqSq θ)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, smul_add]
  rw [trace_HH, trace_HAH, trace_AHH, T4_eq]
  ring

/-- **`S₂ = −(u⁴/Δ²)‖Cθ‖²`** for every `θ`: the `Σθ²` terms cancel because `Δ = a² − 5u²`. -/
theorem S2_eq (u a : ℝ) (θ : Fin 40 → ℝ) (hΔ : a ^ 2 - 5 * u ^ 2 ≠ 0) :
    S2 u a θ = ((-(u ^ 4 / (a ^ 2 - 5 * u ^ 2) ^ 2) * plaqSq θ : ℝ) : ℂ) := by
  have h1 : toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) + u • sadj)) *
      (((-1 / 2 : ℝ) : ℂ) • toC (Wm θ)) =
      ((-1 / 2 : ℝ) : ℂ) • toC (((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * Wm θ) := by
    rw [Matrix.mul_smul, map_mul]
  have h2 : toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • (1 : Matrix (Fin 16) (Fin 16) ℝ) + u • sadj)) *
      (I • toC (Hm θ)) * toC ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * (I • toC (Hm θ)) =
      (I * I) • toC (((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * Hm θ *
        ((a ^ 2 - 5 * u ^ 2)⁻¹ • (a • 1 + u • sadj)) * Hm θ) := by
    rw [map_mul, map_mul, map_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [S2, h1, h2, Matrix.trace_smul, Matrix.trace_smul, trace_toC, trace_toC, trace_KW, trace_KHKH,
    I_mul_I, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- **`u⁴/Δ² = κ(w)/2`** with `κ(w) = 2w⁴/(1 − 5w²)²`, `w = u/a`. -/
theorem kappa_eq (u a : ℝ) (ha : a ≠ 0) (h5 : 1 - 5 * (u / a) ^ 2 ≠ 0) :
    u ^ 4 / (a ^ 2 - 5 * u ^ 2) ^ 2 = (2 * (u / a) ^ 4 / (1 - 5 * (u / a) ^ 2) ^ 2) / 2 := by
  have hΔ : a ^ 2 - 5 * u ^ 2 ≠ 0 := by
    intro h
    apply h5
    field_simp
    linarith
  field_simp

/-- **`κ(1/4) = 1/200`:** at `u = 1/4`, `a = 1 + 4u² = 5/4`, `w = u/a = 1/5`. -/
theorem kappa_quarter :
    (1 / 4 : ℝ) / (1 + 4 * (1 / 4) ^ 2) = 1 / 5 ∧
      2 * (1 / 5 : ℝ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      (1 / 4 : ℝ) ^ 4 / ((1 + 4 * (1 / 4) ^ 2) ^ 2 - 5 * (1 / 4) ^ 2) ^ 2 = 1 / 400 := by
  norm_num

end Comparison

end
