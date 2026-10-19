import Comparison.System.Existence.LastDirection

/-!
# The proof system, the existence layer: the thirteen and the twelve span (Proposition 47)

The rotations that keep a plane `F` and its outside, `u(3) ⊕ u(2)` (`blockTurns F`), have real
dimension 13 and those of trace zero, `s(u(3) ⊕ u(2))` (`blockTurns0 F`), 12: at the plane `{0, 1}` the thirteen
coordinates `Im Z₀₀, Im Z₁₁, Z₀₁, Im Z₂₂, Im Z₃₃, Im Z₄₄, Z₂₃, Z₂₄, Z₃₄` (twelve with trace zero) determine a rotation;
the orthonormal families of `LastDirection.lean` are therefore bases, and a permutation of the lines carries them to every plane.
So the last-step direction's Grams are the forms on `u(3) ⊕ u(2)` and on `s(u(3) ⊕ u(2))` themselves (`prop_47_basis`; at every
unit vector of the plane, `LastDirectionUnit.lean`).
-/

namespace Comparison.System.Existence

open Matrix Complex Polynomial

/-- **`u(3) ⊕ u(2)` at the plane `F`:** anti-Hermitian `5 × 5` matrices with no entry across `F`. -/
noncomputable def blockTurns (F : Finset (Fin 5)) : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℂ) where
  carrier := {Z | Zᴴ = -Z ∧ ∀ a b, (a ∈ F ↔ b ∉ F) → Z a b = 0}
  add_mem' {X Y} hX hY := by
    refine ⟨?_, fun a b h => ?_⟩
    · rw [Matrix.conjTranspose_add, hX.1, hY.1, neg_add]
    · rw [Matrix.add_apply, hX.2 a b h, hY.2 a b h, add_zero]
  zero_mem' := ⟨by simp, fun a b _ => rfl⟩
  smul_mem' c X hX := by
    refine ⟨?_, fun a b h => ?_⟩
    · rw [Matrix.conjTranspose_smul, star_trivial, hX.1, smul_neg]
    · rw [Matrix.smul_apply, hX.2 a b h, smul_zero]

/-- **`s(u(3) ⊕ u(2))` at the plane `F`:** those of trace zero. -/
noncomputable def blockTurns0 (F : Finset (Fin 5)) : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℂ) :=
  blockTurns F ⊓ LinearMap.ker (Matrix.traceLinearMap (Fin 5) ℝ ℂ)

theorem mem_blockTurns (F : Finset (Fin 5)) (Z : Matrix (Fin 5) (Fin 5) ℂ) :
    Z ∈ blockTurns F ↔ Zᴴ = -Z ∧ ∀ a b, (a ∈ F ↔ b ∉ F) → Z a b = 0 := Iff.rfl

theorem mem_blockTurns0 (F : Finset (Fin 5)) (Z : Matrix (Fin 5) (Fin 5) ℂ) :
    Z ∈ blockTurns0 F ↔ (Zᴴ = -Z ∧ ∀ a b, (a ∈ F ↔ b ∉ F) → Z a b = 0) ∧ Z.trace = 0 := by
  rw [blockTurns0, Submodule.mem_inf, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
  rfl

theorem antiHerm_parts {Z : Matrix (Fin 5) (Fin 5) ℂ} (hA : Zᴴ = -Z) (a b : Fin 5) :
    (Z a b).re = -(Z b a).re ∧ (Z a b).im = (Z b a).im := by
  have e := congrFun (congrFun hA b) a
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at e
  have e1 := congrArg Complex.re e
  have e2 := congrArg Complex.im e
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im] at e1 e2
  exact ⟨by linarith, by linarith⟩

/-- The thirteen coordinates of a rotation at the plane `{0, 1}`. -/
noncomputable def coord13 : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] (Fin 13 → ℝ) where
  toFun Z := ![(Z 0 0).im, (Z 1 1).im, (Z 0 1).re, (Z 0 1).im, (Z 2 2).im, (Z 3 3).im, (Z 4 4).im, (Z 2 3).re,
    (Z 2 4).re, (Z 3 4).re, (Z 2 3).im, (Z 2 4).im, (Z 3 4).im]
  map_add' X Y := by
    funext j
    fin_cases j <;> simp
  map_smul' c X := by
    funext j
    fin_cases j <;> simp

/-- The twelve coordinates of a rotation of trace zero at the plane `{0, 1}`. -/
noncomputable def coord12 : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] (Fin 12 → ℝ) where
  toFun Z := ![(Z 0 0).im, (Z 1 1).im, (Z 0 1).re, (Z 0 1).im, (Z 2 2).im, (Z 3 3).im, (Z 2 3).re,
    (Z 2 4).re, (Z 3 4).re, (Z 2 3).im, (Z 2 4).im, (Z 3 4).im]
  map_add' X Y := by
    funext j
    fin_cases j <;> simp
  map_smul' c X := by
    funext j
    fin_cases j <;> simp

theorem plane01_cross : ∀ a b : Fin 5, (a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5))) →
    WholePicture.inPlane a ≠ WholePicture.inPlane b := by
  decide

theorem plane01_same : ∀ a b : Fin 5, ¬(a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5))) →
    (a.val < 2 ↔ b.val < 2) := by
  decide

theorem coord13_injective {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Z ∈ blockTurns {0, 1}) (hc : coord13 Z = 0) :
    Z = 0 := by
  obtain ⟨hA, hB⟩ := hZ
  have hp := antiHerm_parts hA
  have c : ∀ j, coord13 Z j = 0 := fun j => congrFun hc j
  have c0 : (Z 0 0).im = 0 := c 0
  have c1 : (Z 1 1).im = 0 := c 1
  have c2 : (Z 0 1).re = 0 := c 2
  have c3 : (Z 0 1).im = 0 := c 3
  have c4 : (Z 2 2).im = 0 := c 4
  have c5 : (Z 3 3).im = 0 := c 5
  have c6 : (Z 4 4).im = 0 := c 6
  have c7 : (Z 2 3).re = 0 := c 7
  have c8 : (Z 2 4).re = 0 := c 8
  have c9 : (Z 3 4).re = 0 := c 9
  have c10 : (Z 2 3).im = 0 := c 10
  have c11 : (Z 2 4).im = 0 := c 11
  have c12 : (Z 3 4).im = 0 := c 12
  ext a b
  rw [Matrix.zero_apply]
  by_cases hx : (a ∈ ({0, 1} : Finset (Fin 5)) ↔ b ∉ ({0, 1} : Finset (Fin 5)))
  · exact hB a b hx
  · have h5 : ∀ x : Fin 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
    rcases h5 a with rfl | rfl | rfl | rfl | rfl <;> rcases h5 b with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact (hx (by decide)).elim
    | (refine Complex.ext ?_ ?_ <;> simp only [Complex.zero_re, Complex.zero_im] <;>
        linarith [(hp 0 0).1, (hp 1 1).1, (hp 2 2).1, (hp 3 3).1, (hp 4 4).1, (hp 1 0).1, (hp 1 0).2,
          (hp 3 2).1, (hp 3 2).2, (hp 4 2).1, (hp 4 2).2, (hp 4 3).1, (hp 4 3).2])

theorem coord12_injective {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Z ∈ blockTurns0 {0, 1}) (hc : coord12 Z = 0) :
    Z = 0 := by
  rw [mem_blockTurns0] at hZ
  obtain ⟨⟨hA, hB⟩, htr⟩ := hZ
  have h44 : (Z 4 4).im = 0 := by
    have ht := congrArg Complex.im htr
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_five, Complex.add_im, Complex.zero_im] at ht
    have c : ∀ j, coord12 Z j = 0 := fun j => congrFun hc j
    have c0 : (Z 0 0).im = 0 := c 0
    have c1 : (Z 1 1).im = 0 := c 1
    have c4 : (Z 2 2).im = 0 := c 4
    have c5 : (Z 3 3).im = 0 := c 5
    linarith
  have hc13 : coord13 Z = 0 := by
    have c : ∀ j, coord12 Z j = 0 := fun j => congrFun hc j
    funext j
    fin_cases j
    exacts [c 0, c 1, c 2, c 3, c 4, c 5, h44, c 6, c 7, c 8, c 9, c 10, c 11]
  exact coord13_injective ⟨hA, hB⟩ hc13

theorem finrank_blockTurns01_le : Module.finrank ℝ (blockTurns {0, 1}) ≤ 13 := by
  have hinj : Function.Injective (coord13.comp (blockTurns {0, 1}).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Z hZ
    exact Subtype.ext (coord13_injective Z.2 hZ)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

theorem finrank_blockTurns0_01_le : Module.finrank ℝ (blockTurns0 {0, 1}) ≤ 12 := by
  have hinj : Function.Injective (coord12.comp (blockTurns0 {0, 1}).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Z hZ
    exact Subtype.ext (coord12_injective Z.2 hZ)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- The real product `⟨X, Y⟩ = Re tr(X†Y)` as a linear form in `Y`. -/
noncomputable def pairWith (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] ℝ where
  toFun Y := (Xᴴ * Y).trace.re
  map_add' Y Y' := by rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  map_smul' c Y := by
    rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, RingHom.id_apply, smul_eq_mul]

theorem orthonormal_linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Matrix (Fin 5) (Fin 5) ℂ)
    (hT : ∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) : LinearIndependent ℝ T := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (pairWith (T i)) hg
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk, hT, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h

theorem turn13_mem (j : Fin 13) : turn13 j ∈ blockTurns {0, 1} :=
  ⟨turn13_antiHermitian j, fun a b h => turn13_block j a b (plane01_cross a b h)⟩

theorem gen12_mem (j : Fin 12) : WholePicture.gen12 j ∈ blockTurns0 {0, 1} := by
  rw [mem_blockTurns0]
  exact ⟨⟨WholePicture.gen12_antiHermitian j, fun a b h => WholePicture.gen12_block j a b (plane01_cross a b h)⟩,
    WholePicture.gen12_trace j⟩

theorem turn13_span : Submodule.span ℝ (Set.range turn13) = blockTurns {0, 1} := by
  have hli := orthonormal_linearIndependent turn13 turn13_orthonormal
  let T' : Fin 13 → blockTurns {0, 1} := fun j => ⟨turn13 j, turn13_mem j⟩
  have hli' : LinearIndependent ℝ T' :=
    LinearIndependent.of_comp (blockTurns {0, 1}).subtype hli
  have hcard : Fintype.card (Fin 13) = Module.finrank ℝ (blockTurns {0, 1}) := by
    have h1 := hli'.fintype_card_le_finrank
    have h2 := finrank_blockTurns01_le
    simp only [Fintype.card_fin] at h1 ⊢
    omega
  have htop := hli'.span_eq_top_of_card_eq_finrank' hcard
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact turn13_mem j
  · intro Z hZ
    have hZ' : (⟨Z, hZ⟩ : blockTurns {0, 1}) ∈ Submodule.span ℝ (Set.range T') := by rw [htop]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span (blockTurns {0, 1}).subtype hZ'
    rw [← Set.range_comp] at this
    exact this

theorem gen12_span : Submodule.span ℝ (Set.range WholePicture.gen12) = blockTurns0 {0, 1} := by
  have hli := orthonormal_linearIndependent WholePicture.gen12 WholePicture.gen12_orthonormal
  let T' : Fin 12 → blockTurns0 {0, 1} := fun j => ⟨WholePicture.gen12 j, gen12_mem j⟩
  have hli' : LinearIndependent ℝ T' :=
    LinearIndependent.of_comp (blockTurns0 {0, 1}).subtype hli
  have hcard : Fintype.card (Fin 12) = Module.finrank ℝ (blockTurns0 {0, 1}) := by
    have h1 := hli'.fintype_card_le_finrank
    have h2 := finrank_blockTurns0_01_le
    simp only [Fintype.card_fin] at h1 ⊢
    omega
  have htop := hli'.span_eq_top_of_card_eq_finrank' hcard
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact gen12_mem j
  · intro Z hZ
    have hZ' : (⟨Z, hZ⟩ : blockTurns0 {0, 1}) ∈ Submodule.span ℝ (Set.range T') := by rw [htop]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span (blockTurns0 {0, 1}).subtype hZ'
    rw [← Set.range_comp] at this
    exact this

/-! ## Carried to every plane -/

/-- `moveTo σ` as a real-linear map. -/
noncomputable def moveLin (σ : Equiv.Perm (Fin 5)) : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℂ where
  toFun := moveTo σ
  map_add' X Y := rfl
  map_smul' c X := rfl

theorem moveTo_inv (σ : Equiv.Perm (Fin 5)) (X : Matrix (Fin 5) (Fin 5) ℂ) : moveTo σ (moveTo σ⁻¹ X) = X := by
  ext a b
  simp [moveTo, Equiv.Perm.inv_def]

theorem moveTo_block {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k)
    {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Z ∈ blockTurns {h, k}) : moveTo σ⁻¹ Z ∈ blockTurns {0, 1} := by
  obtain ⟨hA, hB⟩ := hZ
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [moveTo_conjTranspose, hA, moveTo_neg]
  · change Z (σ⁻¹.symm a) (σ⁻¹.symm b) = 0
    apply hB
    have ha : ∀ x : Fin 5, (σ⁻¹.symm x ∈ ({h, k} : Finset (Fin 5)) ↔ x ∈ ({0, 1} : Finset (Fin 5))) := by
      intro x
      have hx : σ⁻¹.symm x = σ x := rfl
      rw [hx, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton, ← h0, ← h1,
        σ.injective.eq_iff, σ.injective.eq_iff]
    rw [ha, ha]
    exact hab

theorem span_at_plane {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k)
    {ι : Type*} (T : ι → Matrix (Fin 5) (Fin 5) ℂ) (hT : Submodule.span ℝ (Set.range T) = blockTurns {0, 1})
    {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Z ∈ blockTurns {h, k}) :
    Z ∈ Submodule.span ℝ (Set.range fun j => moveTo σ (T j)) := by
  have hZ' : moveTo σ⁻¹ Z ∈ Submodule.span ℝ (Set.range T) := by rw [hT]; exact moveTo_block h0 h1 hZ
  have := Submodule.apply_mem_span_image_of_mem_span (moveLin σ) hZ'
  rw [← Set.range_comp] at this
  have e : moveLin σ (moveTo σ⁻¹ Z) = Z := moveTo_inv σ Z
  rw [e] at this
  exact this

theorem span_at_plane0 {σ : Equiv.Perm (Fin 5)} {h k : Fin 5} (h0 : σ 0 = h) (h1 : σ 1 = k)
    {ι : Type*} (T : ι → Matrix (Fin 5) (Fin 5) ℂ) (hT : Submodule.span ℝ (Set.range T) = blockTurns0 {0, 1})
    {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Z ∈ blockTurns0 {h, k}) :
    Z ∈ Submodule.span ℝ (Set.range fun j => moveTo σ (T j)) := by
  rw [mem_blockTurns0] at hZ
  have hZ' : moveTo σ⁻¹ Z ∈ Submodule.span ℝ (Set.range T) := by
    rw [hT, mem_blockTurns0]
    exact ⟨moveTo_block h0 h1 hZ.1, by rw [moveTo_trace, hZ.2]⟩
  have := Submodule.apply_mem_span_image_of_mem_span (moveLin σ) hZ'
  rw [← Set.range_comp] at this
  have e : moveLin σ (moveTo σ⁻¹ Z) = Z := moveTo_inv σ Z
  rw [e] at this
  exact this

/-- Proposition 47 at the last-step direction's line `e_h`, with the bases (`LastDirectionUnit.lean`: `prop_47`, at every unit vector of
the plane): the mass form of the division of a real line is
`M_h(X, Y) = 2⟨Xh, Yh⟩`, on `ℂ⁵ = ℝ¹⁰` `M_h(X, X) = 2|Xh|²`; for every plane `{h, k}` thirteen orthonormal rotations that
span `u(3) ⊕ u(2)` (the anti-Hermitian matrices with no entry across `{h, k}`), on which
`½M_h(X_i, X_j) = Re⟨X_ih, X_jh⟩ = diag(1, 0, ½, ½, 0, …, 0)`: three of thirteen move the last-step direction, `w_h = 3/13`,
`χ_h = 30/169`; twelve orthonormal rotations that span `s(u(3) ⊕ u(2))`, on which the form has
`det(x − G) = x⁹(x − ½)²(x − 4/5)`; `(½)/(4/5) = 5/8`, `sin²θ = 3/8`.

Recognition: the last-step direction moves `W⁺`, `W⁻` and `Z` (`½, ½, 4/5`); nine stay massless, the photon and the eight colour
rotations; the last-step direction's length is the Higgs scalar; at the source `M_W²/M_Z² = 5/8`, `sin²θ_W = 3/8`. Uses Props. 21, 39,
46, Definition 27. -/
theorem prop_47_basis :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (X Y : Matrix ι ι ℝ), h ⬝ᵥ h = 1 → Xᵀ = -X →
      Yᵀ = -Y → massFormLine h X Y = 2 * ((X *ᵥ h) ⬝ᵥ (Y *ᵥ h))) ∧
    (∀ (v : Fin 5 → ℂ) (X : Matrix (Fin 5) (Fin 5) ℂ), star v ⬝ᵥ v = 1 → Xᴴ = -X →
      massFormLine (realVec v) (realify X) (realify X) = 2 * (star (X *ᵥ v) ⬝ᵥ (X *ᵥ v)).re) ∧
    (∀ h k : Fin 5, h ≠ k → ∃ T : Fin 13 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, T j ∈ blockTurns {h, k}) ∧
      (∀ Z ∈ blockTurns {h, k}, Z ∈ Submodule.span ℝ (Set.range T)) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (∀ i j, (star (T i *ᵥ lastDirectionAt h) ⬝ᵥ (T j *ᵥ lastDirectionAt h)).re = if i = j then w13 i else 0)) ∧
    ((Finset.univ.filter fun j => w13Z j ≠ 0).card = 3 ∧ (∀ j, w13 j = (w13Z j : ℝ) / norm13 j) ∧
      (3 : ℚ) / 13 * (1 - 3 / 13) = 30 / 169) ∧
    (∀ h k : Fin 5, h ≠ k → ∃ T : Fin 12 → Matrix (Fin 5) (Fin 5) ℂ,
      (∀ j, T j ∈ blockTurns0 {h, k}) ∧
      (∀ Z ∈ blockTurns0 {h, k}, Z ∈ Submodule.span ℝ (Set.range T)) ∧
      (∀ i j, ((T i)ᴴ * T j).trace.re = if i = j then 1 else 0) ∧
      (Matrix.of fun i j => (star (T i *ᵥ lastDirectionAt h) ⬝ᵥ (T j *ᵥ lastDirectionAt h)).re).charpoly =
        X ^ 9 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ))) ∧
    ((1 / 2 : ℝ) / (4 / 5) = 5 / 8 ∧ 1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8) := by
  obtain ⟨p1, p2, -, p4, -, p6⟩ := prop_47_core
  have hhand : ∀ {σ : Equiv.Perm (Fin 5)} {h : Fin 5}, σ 0 = h → ∀ X Y : Matrix (Fin 5) (Fin 5) ℂ,
      star (moveTo σ X *ᵥ lastDirectionAt h) ⬝ᵥ (moveTo σ Y *ᵥ lastDirectionAt h) =
        star (X *ᵥ Pi.single 0 1) ⬝ᵥ (Y *ᵥ Pi.single 0 1) := by
    intro σ h h0 X Y
    rw [lastDirectionAt, ← h0, moveTo_mulVec_single, moveTo_mulVec_single, dot_comp]
  have horth : ∀ (σ : Equiv.Perm (Fin 5)) (X Y : Matrix (Fin 5) (Fin 5) ℂ),
      ((moveTo σ X)ᴴ * moveTo σ Y).trace = (Xᴴ * Y).trace := by
    intro σ X Y
    rw [moveTo_conjTranspose, moveTo_mul, moveTo_trace]
  have hmem : ∀ {σ : Equiv.Perm (Fin 5)} {h k : Fin 5}, σ 0 = h → σ 1 = k → ∀ X, X ∈ blockTurns {0, 1} →
      moveTo σ X ∈ blockTurns {h, k} := by
    intro σ h k h0 h1 X hX
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
  refine ⟨p1, p2, fun h k hk => ?_, p4, fun h k hk => ?_, p6⟩
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    refine ⟨fun j => moveTo σ (turn13 j), fun j => hmem h0 h1 _ (turn13_mem j),
      fun Z hZ => span_at_plane h0 h1 turn13 turn13_span hZ, fun i j => ?_, fun i j => ?_⟩
    · dsimp only
      rw [horth, turn13_orthonormal]
    · dsimp only
      rw [hhand h0, turn13_lastDirection]
  · obtain ⟨σ, h0, h1⟩ := exists_perm h k hk
    refine ⟨fun j => moveTo σ (WholePicture.gen12 j), fun j => ?_,
      fun Z hZ => span_at_plane0 h0 h1 WholePicture.gen12 gen12_span hZ, fun i j => ?_, ?_⟩
    · rw [mem_blockTurns0]
      have hj := gen12_mem j
      rw [mem_blockTurns0] at hj
      exact ⟨hmem h0 h1 _ hj.1, by rw [moveTo_trace, hj.2]⟩
    · dsimp only
      rw [horth, WholePicture.gen12_orthonormal]
    · have hG : (Matrix.of fun i j => (star (moveTo σ (WholePicture.gen12 i) *ᵥ lastDirectionAt h) ⬝ᵥ
          (moveTo σ (WholePicture.gen12 j) *ᵥ lastDirectionAt h)).re) = WholePicture.lastDirectionGram := by
        ext i j
        rw [Matrix.of_apply, hhand h0]
        rfl
      rw [hG, WholePicture.lastDirectionGram_charpoly]

end Comparison.System.Existence
