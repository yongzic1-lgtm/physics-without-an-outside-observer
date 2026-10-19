import Comparison.System.Existence.LastDirectionSpan

/-!
# The proof system, the existence layer: the last-step direction at every unit vector of the plane (Proposition 47)

For a unit vector `v = p e_h + q e_k` of the plane `F = {h, k}`, the unitary
`U = [[p, −q̄], [q, p̄]] ⊕ 1` of the plane `{0, 1}` (`planeU`), carried to `{h, k}` by a permutation of the lines, keeps
the plane and its outside, so `X ↦ UXU†` (`conjU`) maps `u(3) ⊕ u(2)` and `s(u(3) ⊕ u(2))` onto themselves
(`span_conj`, `span_conj0`), keeps the trace form (`conjU_trace_form`) and carries `e₀` to `v`: the thirteen and the
twelve orthonormal rotations `UT_jU†` have at `v` the Grams the rotations `T_j` have at `e₀` (`gram_at_plane`).
-/

namespace Comparison.System.Existence

open Matrix Complex Polynomial

/-- The unitary of the plane `{0, 1}` that carries `e₀` to `p e₀ + q e₁`. -/
noncomputable def planeU (p q : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![p, -(starRingEnd ℂ) q, 0, 0, 0;
     q, (starRingEnd ℂ) p, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

theorem planeU_unitary (p q : ℂ) (hpq : (starRingEnd ℂ) p * p + (starRingEnd ℂ) q * q = 1) :
    (planeU p q)ᴴ * planeU p q = 1 ∧ planeU p q * (planeU p q)ᴴ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [planeU, Matrix.mul_apply, Fin.sum_univ_five, Matrix.conjTranspose_apply, Matrix.one_apply] <;>
    first | rfl | ring1 | linear_combination hpq

theorem planeU_block (p q : ℂ) :
    ∀ a b : Fin 5, (a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5))) → planeU p q a b = 0 := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [planeU]

theorem planeU_col (p q : ℂ) : planeU p q *ᵥ Pi.single 0 1 = ![p, q, 0, 0, 0] := by
  funext a
  fin_cases a <;> simp [planeU, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Pi.single_apply]

/-- A unitary keeps `⟨x, y⟩`. -/
theorem unitary_dot {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : Uᴴ * U = 1) (x y : Fin 5 → ℂ) :
    star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- Conjugation by `U`, `X ↦ UXU†`, real-linear. -/
noncomputable def conjU (U : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℂ where
  toFun X := U * X * Uᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem conjU_apply (U X : Matrix (Fin 5) (Fin 5) ℂ) : conjU U X = U * X * Uᴴ := rfl

theorem block_mul {F : Finset (Fin 5)} {A B : Matrix (Fin 5) (Fin 5) ℂ}
    (hA : ∀ a b, (a ∈ F ↔ b ∉ F) → A a b = 0) (hB : ∀ a b, (a ∈ F ↔ b ∉ F) → B a b = 0) :
    ∀ a b, (a ∈ F ↔ b ∉ F) → (A * B) a b = 0 := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : (a ∈ F ↔ c ∉ F)
  · rw [hA a c hac, zero_mul]
  · have hcb : (c ∈ F ↔ b ∉ F) := by tauto
    rw [hB c b hcb, mul_zero]

theorem block_conjTranspose {F : Finset (Fin 5)} {A : Matrix (Fin 5) (Fin 5) ℂ}
    (hA : ∀ a b, (a ∈ F ↔ b ∉ F) → A a b = 0) : ∀ a b, (a ∈ F ↔ b ∉ F) → Aᴴ a b = 0 := by
  intro a b hab
  rw [Matrix.conjTranspose_apply, hA b a (by tauto), star_zero]

theorem conjU_mem {U X : Matrix (Fin 5) (Fin 5) ℂ} {F : Finset (Fin 5)}
    (hU : ∀ a b, (a ∈ F ↔ b ∉ F) → U a b = 0) (hX : X ∈ blockTurns F) : conjU U X ∈ blockTurns F := by
  obtain ⟨hA, hB⟩ := hX
  refine ⟨?_, block_mul (block_mul hU hB) (block_conjTranspose hU)⟩
  change (U * X * Uᴴ)ᴴ = -(U * X * Uᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_assoc]

theorem conjU_trace {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : Uᴴ * U = 1) (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (conjU U X).trace = X.trace := by
  rw [conjU_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem conjU_mem0 {U X : Matrix (Fin 5) (Fin 5) ℂ} {F : Finset (Fin 5)} (hU1 : Uᴴ * U = 1)
    (hU : ∀ a b, (a ∈ F ↔ b ∉ F) → U a b = 0) (hX : X ∈ blockTurns0 F) : conjU U X ∈ blockTurns0 F := by
  rw [mem_blockTurns0] at hX ⊢
  exact ⟨conjU_mem hU hX.1, by rw [conjU_trace hU1, hX.2]⟩

/-- **Conjugation by a unitary keeps the trace form** `tr(X†Y)`. -/
theorem conjU_trace_form {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : Uᴴ * U = 1) (X Y : Matrix (Fin 5) (Fin 5) ℂ) :
    ((conjU U X)ᴴ * conjU U Y).trace = (Xᴴ * Y).trace := by
  have e : (conjU U X)ᴴ * conjU U Y = U * (Xᴴ * Y * Uᴴ) := by
    rw [conjU_apply, conjU_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc U * (Xᴴ * Uᴴ) * (U * Y * Uᴴ) = U * (Xᴴ * (Uᴴ * U) * Y * Uᴴ) := by noncomm_ring
      _ = U * (Xᴴ * Y * Uᴴ) := by rw [hU, Matrix.mul_one]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem conjU_back {U : Matrix (Fin 5) (Fin 5) ℂ} (hU2 : U * Uᴴ = 1) (Z : Matrix (Fin 5) (Fin 5) ℂ) :
    conjU U (conjU Uᴴ Z) = Z := by
  rw [conjU_apply, conjU_apply, Matrix.conjTranspose_conjTranspose]
  calc U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) := by noncomm_ring
    _ = Z := by rw [hU2, Matrix.one_mul, Matrix.mul_one]

/-- **Conjugation by a unitary that keeps the plane carries a spanning family of `u(3) ⊕ u(2)` to one.** -/
theorem span_conj {U : Matrix (Fin 5) (Fin 5) ℂ} (hU2 : U * Uᴴ = 1)
    (hB : ∀ a b, (a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5))) → U a b = 0)
    {ι : Type*} (T : ι → Matrix (Fin 5) (Fin 5) ℂ) (hT : Submodule.span ℝ (Set.range T) = blockTurns {0, 1}) :
    Submodule.span ℝ (Set.range fun j => conjU U (T j)) = blockTurns {0, 1} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : T j ∈ blockTurns {0, 1} := by
      rw [← hT]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact conjU_mem hB hj
  · intro Z hZ
    have hZ' : conjU Uᴴ Z ∈ Submodule.span ℝ (Set.range T) := by
      rw [hT]
      exact conjU_mem (block_conjTranspose hB) hZ
    have := Submodule.apply_mem_span_image_of_mem_span (conjU U) hZ'
    rw [← Set.range_comp, conjU_back hU2] at this
    exact this

theorem span_conj0 {U : Matrix (Fin 5) (Fin 5) ℂ} (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hB : ∀ a b, (a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5))) → U a b = 0)
    {ι : Type*} (T : ι → Matrix (Fin 5) (Fin 5) ℂ) (hT : Submodule.span ℝ (Set.range T) = blockTurns0 {0, 1}) :
    Submodule.span ℝ (Set.range fun j => conjU U (T j)) = blockTurns0 {0, 1} := by
  have hU1' : Uᴴᴴ * Uᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : T j ∈ blockTurns0 {0, 1} := by
      rw [← hT]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact conjU_mem0 hU1 hB hj
  · intro Z hZ
    have hZ' : conjU Uᴴ Z ∈ Submodule.span ℝ (Set.range T) := by
      rw [hT]
      exact conjU_mem0 hU1' (block_conjTranspose hB) hZ
    have := Submodule.apply_mem_span_image_of_mem_span (conjU U) hZ'
    rw [← Set.range_comp, conjU_back hU2] at this
    exact this

theorem moveTo_mem {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k)
    {X : Matrix (Fin 5) (Fin 5) ℂ} (hX : X ∈ blockTurns {0, 1}) : moveTo σ X ∈ blockTurns {h, k} := by
  obtain ⟨hA, hB⟩ := hX
  refine ⟨by rw [moveTo_conjTranspose, hA, moveTo_neg], fun a b hab => ?_⟩
  change X (σ.symm a) (σ.symm b) = 0
  apply hB
  have ha : ∀ x : Fin 5, (σ.symm x ∈ ({0, 1} : Finset (Fin 5)) ↔ x ∈ ({h, k} : Finset (Fin 5))) := by
    intro x
    rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton, Equiv.symm_apply_eq,
      Equiv.symm_apply_eq, h0, h1]
  rw [ha, ha]
  exact hab

theorem moveTo_mem0 {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k)
    {X : Matrix (Fin 5) (Fin 5) ℂ} (hX : X ∈ blockTurns0 {0, 1}) : moveTo σ X ∈ blockTurns0 {h, k} := by
  rw [mem_blockTurns0] at hX ⊢
  exact ⟨moveTo_mem h0 h1 hX.1, by rw [moveTo_trace, hX.2]⟩

theorem moveTo_mulVec (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) (v : Fin 5 → ℂ) :
    moveTo σ X *ᵥ v = fun i => (X *ᵥ fun a => v (σ a)) (σ.symm i) := by
  funext i
  simp only [moveTo, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Fintype.sum_equiv σ.symm _ _ fun b => by rw [Equiv.apply_symm_apply]

/-- **The Gram at `v` of the carried rotations is the Gram at `e₀` of the rotations.** -/
theorem gram_at_plane (σ : Equiv.Perm (Fin 5)) {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : Uᴴ * U = 1)
    (v : Fin 5 → ℂ) (hv : U *ᵥ Pi.single 0 1 = fun a => v (σ a)) (X Y : Matrix (Fin 5) (Fin 5) ℂ) :
    star (moveTo σ (conjU U X) *ᵥ v) ⬝ᵥ (moveTo σ (conjU U Y) *ᵥ v) =
      star (X *ᵥ Pi.single 0 1) ⬝ᵥ (Y *ᵥ Pi.single 0 1) := by
  rw [moveTo_mulVec, moveTo_mulVec, dot_comp]
  have e : ∀ Z : Matrix (Fin 5) (Fin 5) ℂ, conjU U Z *ᵥ (fun a => v (σ a)) = U *ᵥ (Z *ᵥ Pi.single 0 1) := by
    intro Z
    rw [conjU_apply, ← hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  rw [e, e, unitary_dot hU]

theorem col_eq {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k) (v : Fin 5 → ℂ)
    (hv : ∀ a, a ≠ h → a ≠ k → v a = 0) : planeU (v h) (v k) *ᵥ Pi.single 0 1 = fun a => v (σ a) := by
  rw [planeU_col]
  have hz : ∀ a : Fin 5, a ≠ 0 → a ≠ 1 → v (σ a) = 0 := by
    intro a ha0 ha1
    apply hv
    · rw [← h0]
      exact fun e => ha0 (σ.injective e)
    · rw [← h1]
      exact fun e => ha1 (σ.injective e)
  funext a
  fin_cases a
  · simp [h0]
  · simp [h1]
  · simp [hz 2 (by decide) (by decide)]
  · simp [hz 3 (by decide) (by decide)]
  · simp [hz 4 (by decide) (by decide)]

theorem unit_plane {h k : Fin 5} (hk : h ≠ k) (v : Fin 5 → ℂ) (hv : ∀ a, a ≠ h → a ≠ k → v a = 0)
    (hn : star v ⬝ᵥ v = 1) : (starRingEnd ℂ) (v h) * v h + (starRingEnd ℂ) (v k) * v k = 1 := by
  have hs : star v ⬝ᵥ v = star (v h) * v h + star (v k) * v k := by
    rw [dotProduct]
    exact Finset.sum_eq_add h k hk (fun c _ hc => by simp [hv c hc.1 hc.2])
      (fun h' => absurd (Finset.mem_univ h) h') (fun h' => absurd (Finset.mem_univ k) h')
  rw [hs] at hn
  simpa [Complex.star_def] using hn

/-! ## Proposition 47 -/

/-- **Proposition 47 (the last-step direction).** The mass form of the division of a real line is `M_h(X, Y) = 2⟨Xh, Yh⟩`, on
`ℂ⁵ = ℝ¹⁰` `M_v(X, Y) = 2 Re⟨Xv, Yv⟩` for anti-Hermitian `X`, `Y`, so `M_v(X, X) = 2|Xv|²`, and `½M_v` is the
Gram `Re⟨Xv, Yv⟩`; for every plane `F = {h, k}` and every unit vector `v`
of `F`: thirteen rotations that span `u(3) ⊕ u(2)` (the anti-Hermitian matrices with no entry across `F`), orthonormal
for `Re tr(X†Y)`, on which `½M_v(X_i, X_j) = Re⟨X_iv, X_jv⟩ = diag(1, 0, ½, ½, 0, …, 0)`: three of thirteen move
the last-step direction, `w_h = 3/13`, `χ_h = w_h(1 − w_h) = 30/169`; and twelve orthonormal rotations that span `s(u(3) ⊕ u(2))`, on
which the form has `det(x − G) = x⁹(x − ½)²(x − 4/5)`: `½M_v = 4/5, ½, ½, 0⁹`; `(½)/(4/5) = 5/8`,
`sin²θ = 1 − 5/8 = 3/8`.

Recognition: the last-step direction moves `W⁺`, `W⁻` and `Z` (`½, ½, 4/5`); nine stay massless, the photon and the eight colour
rotations; the last-step direction's length is the Higgs scalar; at the source `M_W²/M_Z² = 5/8`, `sin²θ_W = 3/8`. Uses Props. 21, 39,
46, Definition 27. -/
theorem prop_47 :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (X Y : Matrix ι ι ℝ), h ⬝ᵥ h = 1 → Xᵀ = -X →
      Yᵀ = -Y → massFormLine h X Y = 2 * ((X *ᵥ h) ⬝ᵥ (Y *ᵥ h))) ∧
    (∀ (v : Fin 5 → ℂ) (X Y : Matrix (Fin 5) (Fin 5) ℂ), star v ⬝ᵥ v = 1 → Xᴴ = -X → Yᴴ = -Y →
      massFormLine (realVec v) (realify X) (realify Y) = 2 * (star (X *ᵥ v) ⬝ᵥ (Y *ᵥ v)).re) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ v : Fin 5 → ℂ, (∀ a, a ≠ h → a ≠ k → v a = 0) → star v ⬝ᵥ v = 1 →
      ∃ T : Fin 13 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, T j ∈ blockTurns {h, k}) ∧
      (∀ Z ∈ blockTurns {h, k}, Z ∈ Submodule.span ℝ (Set.range T)) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (∀ i j, (star (T i *ᵥ v) ⬝ᵥ (T j *ᵥ v)).re = if i = j then w13 i else 0)) ∧
    ((Finset.univ.filter fun j => w13Z j ≠ 0).card = 3 ∧ (∀ j, w13 j = (w13Z j : ℝ) / norm13 j) ∧
      (3 : ℚ) / 13 * (1 - 3 / 13) = 30 / 169) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ v : Fin 5 → ℂ, (∀ a, a ≠ h → a ≠ k → v a = 0) → star v ⬝ᵥ v = 1 →
      ∃ T : Fin 12 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, T j ∈ blockTurns0 {h, k}) ∧
      (∀ Z ∈ blockTurns0 {h, k}, Z ∈ Submodule.span ℝ (Set.range T)) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (Matrix.of fun i j => (star (T i *ᵥ v) ⬝ᵥ (T j *ᵥ v)).re).charpoly =
        X ^ 9 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ))) ∧
    ((1 / 2 : ℝ) / (4 / 5) = 5 / 8 ∧ 1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8) := by
  obtain ⟨p1, -, -, p4, -, p6⟩ := prop_47_basis
  refine ⟨p1, fun v X Y hv hX hY => massFormLine_complex v hv X Y hX hY, fun h k hk v hv hn => ?_, p4,
    fun h k hk v hv hn => ?_, p6⟩
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    obtain ⟨hU1, hU2⟩ := planeU_unitary (v h) (v k) (unit_plane hk v hv hn)
    have hcol := col_eq h0 h1 v hv
    refine ⟨fun j => moveTo σ (conjU (planeU (v h) (v k)) (turn13 j)),
      fun j => moveTo_mem h0 h1 (conjU_mem (planeU_block _ _) (turn13_mem j)),
      fun Z hZ => span_at_plane h0 h1 _ (span_conj hU2 (planeU_block _ _) turn13 turn13_span) hZ,
      fun i j => ?_, fun i j => ?_⟩
    · dsimp only
      rw [moveTo_conjTranspose, moveTo_mul, moveTo_trace, conjU_trace_form hU1, turn13_orthonormal]
    · dsimp only
      rw [gram_at_plane σ hU1 v hcol, turn13_lastDirection]
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    obtain ⟨hU1, hU2⟩ := planeU_unitary (v h) (v k) (unit_plane hk v hv hn)
    have hcol := col_eq h0 h1 v hv
    refine ⟨fun j => moveTo σ (conjU (planeU (v h) (v k)) (WholePicture.gen12 j)),
      fun j => moveTo_mem0 h0 h1 (conjU_mem0 hU1 (planeU_block _ _) (gen12_mem j)),
      fun Z hZ => span_at_plane0 h0 h1 _ (span_conj0 hU1 hU2 (planeU_block _ _) WholePicture.gen12 gen12_span) hZ,
      fun i j => ?_, ?_⟩
    · dsimp only
      rw [moveTo_conjTranspose, moveTo_mul, moveTo_trace, conjU_trace_form hU1, WholePicture.gen12_orthonormal]
    · have hG : (Matrix.of fun i j => (star (moveTo σ (conjU (planeU (v h) (v k)) (WholePicture.gen12 i)) *ᵥ v) ⬝ᵥ
          (moveTo σ (conjU (planeU (v h) (v k)) (WholePicture.gen12 j)) *ᵥ v)).re) = WholePicture.lastDirectionGram := by
        ext i j
        rw [Matrix.of_apply, gram_at_plane σ hU1 v hcol]
        rfl
      rw [hG, WholePicture.lastDirectionGram_charpoly]

end Comparison.System.Existence
