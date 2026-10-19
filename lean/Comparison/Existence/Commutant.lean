module

public import Comparison.Existence.Pair
public import Comparison.Existence.Turn

/-!
# Book IX. The rotations of a pair and what each keeps: 45, 25, 24, 12, 9 (Proposition 46)

The ten lines of a pair are
indexed by `Ten = Fin 5 ⊕ Fin 5` (`inl t` the line `t` of the one system, `inr t` that of the other).

**Any ten anticommuting lines** (`IsTen Γ`: `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy` in a real algebra):
* `turnOf Γ M = ρ(M) = ¼ Σ_{x,y} M_xy Γ_xΓ_y`; `turnOf_comm_line`: `[ρ(M), Γ_z] = Σ_x M_xz Γ_x`
  (`M` antisymmetric); `lines_indep`: the ten lines are independent; `turnOf_eq_zero`: `ρ(M) = 0`
  only for `M = 0`; `turnOf_lie`: **`[ρ(M), ρ(N)] = ρ([M, N])`**.
* `turnsTen Γ`: the rotations `ρ(M)`, `M` antisymmetric; `turnsTen_eq_span`: they are the real span of
  the forty-five `½Γ_xΓ_y` (`x < y`); `finrank_turnsTen`: **`so(10)` has dimension 45**.
* `pairSum Γ = Σ_t Γ_tΓ_{5+t}` (`ρ(J) = ½ pairSum`, `J` the complex structure `cxJ` pairing line `t`
  of one system with line `t` of the other); `keepL_eq`: the rotations commuting with `pairSum` are
  `ρ(u(5))`, where `uFive R = [[A, −B], [B, A]]` (`A` antisymmetric, `B` symmetric, `Z = A + iB`
  anti-Hermitian) parametrises `u(5)` injectively by the real `5 × 5` matrices `R`
  (`range_uFive`); `finrank_keepL`: **25**.

**On `H ⊗ H ⊗ ℂ²`** (`tenLine` of `Pair.lean`): `pair_turns_finrank` **45**; `pair_keepL_finrank`:
the rotations keeping the comparison `(L − 1) ⊗ σ_z` (`comparison_as_turn`) are **25**;
`keepL_pair_eq`, `pair_keepL_finrank'`: since every rotation commutes with the chirality `1 ⊗ 1 ⊗ σ_z`,
keeping `L ⊗ 1` (keeping `L` on both halves) is the same: **25**.

**On `Λℂ⁵`** (B.46 (iv)): `fockLine`: `Γ_t = ε_t + ι_t`, `Γ_{5+t} = i(ε_t − ι_t)`;
`fock_comparison`: `−i Σ_t Γ_tΓ_{5+t} = 5 − 2N`;
`fock_normal`: **`ρ(uFive R) = Σ Z_st ε_sι_t − ½ tr Z`**
(`u(5)` acts on the exterior powers twisted by `det^{−1/2}`). With `Ω = f_∅` (`vacF`),
`N_F = N_3 + N_4` (`planeN`, the plane `F = {h, k} = {3, 4}`) and `ℓ_h = f_{0124}` (`lastDirectionRelVec`, the
two-spinor state with `N_h = 0`, `N_k = 1`, `N_C = 3`):
* `turn_vac_iff`: keeping `Ω` is `tr R = 0`; `plane_comm_iff`, `uFive_plane_iff`: keeping `N_F` is
  `R_st = 0` across the plane; `turn_lastDirection_iff`: then keeping `ℓ_h` is `R₃₃ = R₃₄ = R₄₃ = 0`.
* `finrank_su5`, `finrank_plane5`, `finrank_lastDirection5`: these real matrices have dimensions 24, 12, 9.
* `turns_chain`: **`so(10)` 45, keeping `L` 25 (`u(5)`), also `Ω` 24 (`su(5)`), also `N_F` 12
  (`s(u(3) ⊕ u(2))`), also `ℓ_h` 9 (`su(3) ⊕ u(1)`)**, as real dimensions of spaces of operators on
  the spinors of the ten lines.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The ten lines of a pair: `inl t` is the line `t` of the one system, `inr t` that of the other. -/
abbrev Ten := Fin 5 ⊕ Fin 5

section Abstract

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Ten anticommuting lines: `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`. -/
def IsTen (Γ : Ten → A) : Prop :=
  ∀ x y, Γ x * Γ y + Γ y * Γ x = (if x = y then (2 : ℝ) else 0) • (1 : A)

/-- The rotation of the ten lines with the matrix `M`: `ρ(M) = ¼ Σ_{x,y} M_xy Γ_xΓ_y`. -/
noncomputable def turnOf (Γ : Ten → A) : Matrix Ten Ten ℝ →ₗ[ℝ] A where
  toFun M := ∑ x, ∑ y, ((1 / 4 : ℝ) * M x y) • (Γ x * Γ y)
  map_add' M N := by
    simp only [Matrix.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring

theorem turnOf_apply (Γ : Ten → A) (M : Matrix Ten Ten ℝ) :
    turnOf Γ M = ∑ x, ∑ y, ((1 / 4 : ℝ) * M x y) • (Γ x * Γ y) := rfl

theorem triple_comm (Γ : Ten → A) (hΓ : IsTen Γ) (x y z : Ten) :
    Γ x * Γ y * Γ z - Γ z * (Γ x * Γ y) =
      (if y = z then (2 : ℝ) else 0) • Γ x - (if x = z then (2 : ℝ) else 0) • Γ y := by
  have e : Γ x * Γ y * Γ z - Γ z * (Γ x * Γ y) =
      Γ x * (Γ y * Γ z + Γ z * Γ y) - (Γ x * Γ z + Γ z * Γ x) * Γ y := by noncomm_ring
  rw [e, hΓ, hΓ, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

/-- **A rotation moves a line:** `[ρ(M), Γ_z] = Σ_x M_xz Γ_x` for antisymmetric `M`. -/
theorem turnOf_comm_line (Γ : Ten → A) (hΓ : IsTen Γ) (M : Matrix Ten Ten ℝ) (hM : Mᵀ = -M)
    (z : Ten) : turnOf Γ M * Γ z - Γ z * turnOf Γ M = ∑ x, M x z • Γ x := by
  have hs : ∀ x y, M x y = -M y x := fun x y => by
    have := congrFun (congrFun hM y) x
    simpa using this
  have h : ∀ x, (∑ y, ((1 / 4 : ℝ) * M x y) • (Γ x * Γ y)) * Γ z -
      Γ z * ∑ y, ((1 / 4 : ℝ) * M x y) • (Γ x * Γ y) =
      (∑ y, ((1 / 4 : ℝ) * M x y * if y = z then (2 : ℝ) else 0) • Γ x) -
        ∑ y, ((1 / 4 : ℝ) * M x y * if x = z then (2 : ℝ) else 0) • Γ y := by
    intro x
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, triple_comm Γ hΓ, smul_sub, smul_smul,
      smul_smul]
  rw [turnOf_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib]
  have hA : ∑ x, ∑ y, ((1 / 4 : ℝ) * M x y * if y = z then (2 : ℝ) else 0) • Γ x =
      ∑ x, ((1 / 4 : ℝ) * M x z * 2) • Γ x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  have hB : ∑ x, ∑ y, ((1 / 4 : ℝ) * M x y * if x = z then (2 : ℝ) else 0) • Γ y =
      ∑ y, ((1 / 4 : ℝ) * M z y * 2) • Γ y := by
    rw [Finset.sum_eq_single z]
    · simp only [ite_true]
    · intro x _ hx
      simp only [hx, ite_false, mul_zero, zero_smul, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ z) h
  rw [hA, hB]
  have h2 : ∑ y, ((1 / 4 : ℝ) * M z y * 2) • Γ y = -∑ x, ((1 / 4 : ℝ) * M x z * 2) • Γ x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hs z y, ← neg_smul]
    congr 1
    ring
  rw [h2, sub_neg_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← add_smul]
  congr 1
  ring

/-- **The ten lines are independent:** `Σ a_x Γ_x = 0` only for `a = 0`. -/
theorem lines_indep [Nontrivial A] (Γ : Ten → A) (hΓ : IsTen Γ) (a : Ten → ℝ)
    (h : ∑ x, a x • Γ x = 0) : a = 0 := by
  funext z
  have e : Γ z * (∑ x, a x • Γ x) + (∑ x, a x • Γ x) * Γ z = (2 * a z) • (1 : A) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    simp only [mul_smul_comm, smul_mul_assoc, ← smul_add, hΓ z, smul_smul]
    simp only [mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [mul_comm]
  rw [h, mul_zero, zero_mul, add_zero, Algebra.smul_def, mul_one] at e
  have h2 : (2 : ℝ) * a z = 0 := (algebraMap ℝ A).injective (by rw [← e, map_zero])
  simpa using h2

/-- **A rotation is known by its matrix:** `ρ(M) = 0` only for `M = 0` (antisymmetric `M`). -/
theorem turnOf_eq_zero [Nontrivial A] (Γ : Ten → A) (hΓ : IsTen Γ) (M : Matrix Ten Ten ℝ)
    (hM : Mᵀ = -M) (h0 : turnOf Γ M = 0) : M = 0 := by
  ext x z
  have hz := turnOf_comm_line Γ hΓ M hM z
  rw [h0, zero_mul, mul_zero, sub_zero] at hz
  have := congrFun (lines_indep Γ hΓ (fun x => M x z) hz.symm) x
  simpa using this

/-- **The rotations close under the commutator:** `[ρ(M), ρ(N)] = ρ([M, N])`. -/
theorem turnOf_lie (Γ : Ten → A) (hΓ : IsTen Γ) (M N : Matrix Ten Ten ℝ) (hM : Mᵀ = -M) :
    turnOf Γ M * turnOf Γ N - turnOf Γ N * turnOf Γ M = turnOf Γ (M * N - N * M) := by
  have hs : ∀ x y, M x y = -M y x := fun x y => by
    have := congrFun (congrFun hM y) x
    simpa using this
  have hc : ∀ z w, turnOf Γ M * (Γ z * Γ w) - (Γ z * Γ w) * turnOf Γ M =
      (∑ x, M x z • Γ x) * Γ w + Γ z * (∑ x, M x w • Γ x) := by
    intro z w
    rw [← turnOf_comm_line Γ hΓ M hM z, ← turnOf_comm_line Γ hΓ M hM w]
    noncomm_ring
  have e1 : turnOf Γ M * turnOf Γ N - turnOf Γ N * turnOf Γ M =
      ∑ z, ∑ w, ((1 / 4 : ℝ) * N z w) •
        (turnOf Γ M * (Γ z * Γ w) - (Γ z * Γ w) * turnOf Γ M) := by
    rw [turnOf_apply Γ N]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      ← Finset.sum_sub_distrib, ← smul_sub]
  rw [e1]
  simp only [hc, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_add,
    Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [turnOf_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, sub_smul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_smul]
  have h1 : ∑ x, ∑ x_1, ∑ x_2, (1 / 4 * N x x_1 * M x_2 x) • (Γ x_2 * Γ x_1) =
      ∑ x, ∑ x_1, ∑ i, (1 / 4 * (M x i * N i x_1)) • (Γ x * Γ x_1) := by
    calc _ = ∑ z, ∑ a, ∑ w, (1 / 4 * N z w * M a z) • (Γ a * Γ w) :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ a, ∑ z, ∑ w, (1 / 4 * N z w * M a z) • (Γ a * Γ w) := Finset.sum_comm
      _ = ∑ a, ∑ w, ∑ z, (1 / 4 * N z w * M a z) • (Γ a * Γ w) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ =>
          Finset.sum_congr rfl fun z _ => ?_
        congr 1
        ring
  have h2 : ∑ x, ∑ x_1, ∑ x_2, (1 / 4 * N x x_1 * M x_2 x_1) • (Γ x * Γ x_2) =
      -∑ x, ∑ x_1, ∑ i, (1 / 4 * (N x i * M i x_1)) • (Γ x * Γ x_1) := by
    calc _ = ∑ z, ∑ a, ∑ w, (1 / 4 * N z w * M a w) • (Γ z * Γ a) :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hs a w, ← neg_smul]
        congr 1
        ring
  rw [h1, h2, sub_eq_add_neg]

/-- The operators commuting with `C`. -/
def commWith {X : Type*} [Ring X] [Algebra ℝ X] (C : X) : Submodule ℝ X where
  carrier := {Y | Y * C = C * Y}
  add_mem' {Y Z} hY hZ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul, mul_add, hY, hZ]
  zero_mem' := by simp
  smul_mem' c Y hY := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_mul_assoc, mul_smul_comm, hY]

theorem mem_commWith {X : Type*} [Ring X] [Algebra ℝ X] (C Y : X) :
    Y ∈ commWith C ↔ Y * C = C * Y := Iff.rfl

end Abstract

/-! ## The antisymmetric matrices of the ten: forty-five -/

/-- The antisymmetric matrices of the ten. -/
def skewTen : Submodule ℝ (Matrix Ten Ten ℝ) where
  carrier := {M | Mᵀ = -M}
  add_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_add, hM, hN, neg_add]
  zero_mem' := by simp
  smul_mem' c M hM := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_smul, hM, smul_neg]

theorem mem_skewTen (M : Matrix Ten Ten ℝ) : M ∈ skewTen ↔ Mᵀ = -M := Iff.rfl

/-- The order used to list each pair of the ten once: `inl t ↦ t`, `inr t ↦ 5 + t`. -/
def tenCode : Ten → ℕ
  | Sum.inl t => t
  | Sum.inr t => 5 + t

theorem tenCode_injective : Function.Injective tenCode := by decide

/-- The pairs `x < y` of the ten. -/
abbrev TenPairs := {p : Ten × Ten // tenCode p.1 < tenCode p.2}

theorem card_tenPairs : Fintype.card TenPairs = 45 := by decide

/-- The plane rotation `E_xy − E_yx` of the pair `x < y`. -/
noncomputable def planeMat (p : TenPairs) : Matrix Ten Ten ℝ :=
  Matrix.single p.1.1 p.1.2 1 - Matrix.single p.1.2 p.1.1 1

/-- The antisymmetric matrix with the coordinates `c`: `Σ_{x<y} c_xy (E_xy − E_yx)`. -/
noncomputable def skewCoord : (TenPairs → ℝ) →ₗ[ℝ] Matrix Ten Ten ℝ :=
  ∑ p, (LinearMap.proj p : (TenPairs → ℝ) →ₗ[ℝ] ℝ).smulRight (planeMat p)

theorem skewCoord_apply (c : TenPairs → ℝ) : skewCoord c = ∑ p, c p • planeMat p := by
  simp [skewCoord]

theorem skewCoord_entry (c : TenPairs → ℝ) (i j : Ten) :
    skewCoord c i j = (if h : tenCode i < tenCode j then c ⟨(i, j), h⟩ else 0) -
      (if h : tenCode j < tenCode i then c ⟨(j, i), h⟩ else 0) := by
  rw [skewCoord_apply, Matrix.sum_apply]
  simp only [planeMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
      · simp
      · intro q _ hq
        have : ¬(q.1.1 = i ∧ q.1.2 = j) := fun h' => hq (Subtype.ext (Prod.ext h'.1 h'.2))
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun q _ => ?_
      have : ¬(q.1.1 = i ∧ q.1.2 = j) := fun h' => h (h'.1 ▸ h'.2 ▸ q.2)
      simp [this]
  · split_ifs with h
    · rw [Finset.sum_eq_single ⟨(j, i), h⟩]
      · simp
      · intro q _ hq
        have : ¬(q.1.2 = i ∧ q.1.1 = j) := fun h' => hq (Subtype.ext (Prod.ext h'.2 h'.1))
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun q _ => ?_
      have : ¬(q.1.2 = i ∧ q.1.1 = j) := fun h' => h (h'.1 ▸ h'.2 ▸ q.2)
      simp [this]

theorem skewCoord_injective : Function.Injective skewCoord := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext p
  have h := congrFun (congrFun hc p.1.1) p.1.2
  simp only [skewCoord_entry, p.2, lt_asymm p.2, ↓reduceDIte, sub_zero] at h
  exact h

theorem range_skewCoord : LinearMap.range skewCoord = skewTen := by
  ext M
  constructor
  · rintro ⟨c, rfl⟩
    rw [mem_skewTen]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, skewCoord_entry]
    ring
  · intro hM
    rw [mem_skewTen] at hM
    refine ⟨fun p => M p.1.1 p.1.2, ?_⟩
    ext i j
    have hs : M j i = -M i j := by
      have := congrFun (congrFun hM i) j
      simpa using this
    rw [skewCoord_entry]
    rcases lt_trichotomy (tenCode i) (tenCode j) with h | h | h
    · simp only [h, lt_asymm h, ↓reduceDIte, sub_zero]
    · have hij : i = j := tenCode_injective h
      subst hij
      simp only [lt_irrefl, ↓reduceDIte, sub_zero]
      have : M i i = -M i i := hs
      linarith
    · simp only [h, lt_asymm h, ↓reduceDIte, zero_sub, hs, neg_neg]

theorem finrank_skewTen : Module.finrank ℝ skewTen = 45 := by
  rw [← range_skewCoord, LinearMap.finrank_range_of_inj skewCoord_injective,
    Module.finrank_fintype_fun_eq_card, card_tenPairs]

/-! ## The ten paired into five complex lines: twenty-five -/

/-- The complex structure that pairs the line `t` of the one system with the line `t` of the
other. -/
def cxJ : Matrix Ten Ten ℝ := Matrix.fromBlocks 0 1 (-1) 0

/-- The antisymmetric part read from the upper triangle of `R`. -/
def skA (R : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun s t => if s < t then R s t else if t < s then -R t s else 0

/-- The symmetric part read from the lower triangle and the diagonal of `R`. -/
def syB (R : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun s t => if t ≤ s then R s t else R t s

/-- **The rotations of five complex lines:** `R ↦ [[A, −B], [B, A]]`, `A` antisymmetric (from the upper
triangle of `R`), `B` symmetric (from the rest): `Z = A + iB` runs over the anti-Hermitian
`5 × 5` matrices, `u(5)`. -/
def uFive : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix Ten Ten ℝ where
  toFun R := Matrix.fromBlocks (skA R) (-syB R) (syB R) (skA R)
  map_add' R R' := by
    have h1 : skA (R + R') = skA R + skA R' := by
      ext s t
      simp only [skA, Matrix.of_apply, Matrix.add_apply]
      split_ifs <;> ring
    have h2 : syB (R + R') = syB R + syB R' := by
      ext s t
      simp only [syB, Matrix.of_apply, Matrix.add_apply]
      split_ifs <;> ring
    rw [h1, h2, Matrix.fromBlocks_add, neg_add]
  map_smul' c R := by
    have h1 : skA (c • R) = c • skA R := by
      ext s t
      simp only [skA, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    have h2 : syB (c • R) = c • syB R := by
      ext s t
      simp only [syB, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [h1, h2, RingHom.id_apply, Matrix.fromBlocks_smul, smul_neg]

theorem uFive_apply (R : Matrix (Fin 5) (Fin 5) ℝ) :
    uFive R = Matrix.fromBlocks (skA R) (-syB R) (syB R) (skA R) := rfl

theorem skA_transpose (R : Matrix (Fin 5) (Fin 5) ℝ) : (skA R)ᵀ = -skA R := by
  ext s t
  simp only [skA, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
  rcases lt_trichotomy s t with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    simp
  · simp [h, not_lt.mpr h.le]

theorem syB_transpose (R : Matrix (Fin 5) (Fin 5) ℝ) : (syB R)ᵀ = syB R := by
  ext s t
  simp only [syB, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy s t with h | h | h
  · simp [h.le, not_le.mpr h]
  · subst h
    simp
  · simp [h.le, not_le.mpr h]

theorem uFive_mem_skew (R : Matrix (Fin 5) (Fin 5) ℝ) : uFive R ∈ skewTen := by
  rw [mem_skewTen, uFive_apply, Matrix.fromBlocks_transpose, skA_transpose, syB_transpose,
    Matrix.transpose_neg, syB_transpose, Matrix.fromBlocks_neg, neg_neg]

theorem uFive_comm (R : Matrix (Fin 5) (Fin 5) ℝ) : uFive R * cxJ = cxJ * uFive R := by
  rw [uFive_apply, cxJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem uFive_injective : Function.Injective uFive := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro R hR
  rw [uFive_apply, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at hR
  obtain ⟨hA, -, hB, -⟩ := hR
  ext s t
  rcases lt_or_ge s t with h | h
  · have := congrFun (congrFun hA s) t
    simpa [skA, h] using this
  · have := congrFun (congrFun hB s) t
    simpa [syB, h] using this

/-- The antisymmetric matrices that commute with the complex structure. -/
def keepJ : Submodule ℝ (Matrix Ten Ten ℝ) := skewTen ⊓ commWith cxJ

theorem range_uFive : LinearMap.range uFive = keepJ := by
  ext M
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨uFive_mem_skew R, uFive_comm R⟩
  · rintro ⟨hM, hJ⟩
    rw [SetLike.mem_coe, mem_skewTen] at hM
    rw [SetLike.mem_coe, mem_commWith] at hJ
    set P := M.toBlocks₁₁
    set Q := M.toBlocks₁₂
    set R' := M.toBlocks₂₁
    set S := M.toBlocks₂₂
    have hMb : M = Matrix.fromBlocks P Q R' S := (Matrix.fromBlocks_toBlocks M).symm
    rw [hMb, cxJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hJ
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
      Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul] at hJ
    rw [Matrix.fromBlocks_inj] at hJ
    obtain ⟨h1, h2, -, -⟩ := hJ
    rw [hMb, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.fromBlocks_inj] at hM
    obtain ⟨hP, hRQ, -, -⟩ := hM
    have hQ : Q = -R' := by rw [← h1, neg_neg]
    have hS : S = P := h2.symm
    have hR' : R'ᵀ = R' := by
      have := hRQ
      rw [hQ, neg_neg] at this
      exact this
    refine ⟨Matrix.of fun s t => if s < t then P s t else R' s t, ?_⟩
    rw [uFive_apply, hMb, hQ, hS]
    have hA : skA (Matrix.of fun s t => if s < t then P s t else R' s t) = P := by
      ext s t
      simp only [skA, Matrix.of_apply]
      have hPst : P t s = -P s t := by
        have := congrFun (congrFun hP s) t
        simpa using this
      rcases lt_trichotomy s t with h | h | h
      · simp [h]
      · subst h
        have : P s s = -P s s := hPst
        simp only [lt_irrefl, ite_false]
        linarith
      · simp [h, not_lt.mpr h.le, hPst]
    have hB : syB (Matrix.of fun s t => if s < t then P s t else R' s t) = R' := by
      ext s t
      simp only [syB, Matrix.of_apply]
      have hRst : R' t s = R' s t := by
        have := congrFun (congrFun hR' s) t
        simpa using this
      rcases lt_trichotomy s t with h | h | h
      · simp [not_le.mpr h, not_lt.mpr h.le, hRst]
      · subst h
        simp
      · simp [h.le, not_lt.mpr h.le]
    rw [hA, hB]

theorem finrank_keepJ : Module.finrank ℝ keepJ = 25 := by
  rw [← range_uFive, LinearMap.finrank_range_of_inj uFive_injective, Module.finrank_matrix]
  simp

theorem cxJ_transpose : cxJᵀ = -cxJ := by
  rw [cxJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp

/-! ## The rotations of any ten lines, and those that keep the comparison -/

section Turns

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **The rotations of the ten lines**, `so(10)`: the `ρ(M)` with `M` antisymmetric. -/
noncomputable def turnsTen (Γ : Ten → A) : Submodule ℝ A := skewTen.map (turnOf Γ)

/-- `Σ_t Γ_tΓ_{5+t}`: the comparison less one is `−i` times this (`comparison_as_turn`). -/
def pairSum (Γ : Ten → A) : A := ∑ t, Γ (Sum.inl t) * Γ (Sum.inr t)

theorem turnOf_single (Γ : Ten → A) (x y : Ten) :
    turnOf Γ (Matrix.single x y 1) = (1 / 4 : ℝ) • (Γ x * Γ y) := by
  rw [turnOf_apply, Finset.sum_eq_single x, Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm ha]
  · simp

theorem anti_of_ne (Γ : Ten → A) (hΓ : IsTen Γ) {x y : Ten} (h : x ≠ y) :
    Γ y * Γ x = -(Γ x * Γ y) := by
  have := hΓ x y
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), zero_smul] at this
  exact eq_neg_of_add_eq_zero_right this

/-- `ρ(E_xy − E_yx) = ½ Γ_xΓ_y` for `x ≠ y`. -/
theorem turnOf_planeMat (Γ : Ten → A) (hΓ : IsTen Γ) (p : TenPairs) :
    turnOf Γ (planeMat p) = (1 / 2 : ℝ) • (Γ p.1.1 * Γ p.1.2) := by
  have hne : p.1.1 ≠ p.1.2 := fun h => lt_irrefl _ (h ▸ p.2)
  rw [planeMat, map_sub, turnOf_single, turnOf_single, anti_of_ne Γ hΓ hne, smul_neg,
    sub_neg_eq_add, ← add_smul]
  norm_num

theorem planeMat_mem (p : TenPairs) : planeMat p ∈ skewTen := by
  rw [← range_skewCoord]
  refine ⟨Pi.single p 1, ?_⟩
  rw [skewCoord_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

/-- **The forty-five `½Γ_xΓ_y` (`x < y`) span the rotations.** -/
theorem turnsTen_eq_span (Γ : Ten → A) (hΓ : IsTen Γ) :
    turnsTen Γ =
      Submodule.span ℝ (Set.range fun p : TenPairs => (1 / 2 : ℝ) • (Γ p.1.1 * Γ p.1.2)) := by
  apply le_antisymm
  · rintro X ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, ← range_skewCoord] at hM
    obtain ⟨c, rfl⟩ := hM
    rw [skewCoord_apply, map_sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [map_smul, turnOf_planeMat Γ hΓ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rw [Submodule.span_le]
    rintro X ⟨p, rfl⟩
    exact ⟨planeMat p, planeMat_mem p, turnOf_planeMat Γ hΓ p⟩

theorem range_turnOf_skewCoord (Γ : Ten → A) :
    LinearMap.range ((turnOf Γ).comp skewCoord) = turnsTen Γ := by
  rw [LinearMap.range_comp, range_skewCoord, turnsTen]

/-- **`so(10)` has dimension 45.** -/
theorem finrank_turnsTen [Nontrivial A] (Γ : Ten → A) (hΓ : IsTen Γ) :
    Module.finrank ℝ (turnsTen Γ) = 45 := by
  have hinj : Function.Injective ((turnOf Γ).comp skewCoord) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hmem : skewCoord c ∈ skewTen := by rw [← range_skewCoord]; exact ⟨c, rfl⟩
    have h0 := turnOf_eq_zero Γ hΓ (skewCoord c) hmem hc
    exact skewCoord_injective (by rw [h0, map_zero])
  rw [← range_turnOf_skewCoord, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fintype_fun_eq_card, card_tenPairs]

/-- `ρ(J) = ½ Σ_t Γ_tΓ_{5+t}`. -/
theorem turnOf_cxJ (Γ : Ten → A) (hΓ : IsTen Γ) : turnOf Γ cxJ = (1 / 2 : ℝ) • pairSum Γ := by
  rw [turnOf_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, cxJ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply,
    Matrix.neg_apply, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, add_zero, mul_ite,
    mul_one, mul_neg, neg_smul, Finset.sum_neg_distrib, ite_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, pairSum, Finset.smul_sum]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [anti_of_ne Γ hΓ Sum.inl_ne_inr, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

theorem cxJ_comm_skew (M : Matrix Ten Ten ℝ) (hM : Mᵀ = -M) :
    (M * cxJ - cxJ * M)ᵀ = -(M * cxJ - cxJ * M) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hM, cxJ_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_sub]

/-- **The rotations that keep the comparison are those of the complex structure:**
`so(10) ∩ {X : X Σ_tΓ_tΓ_{5+t} = Σ_tΓ_tΓ_{5+t} X} = ρ(u(5))`. -/
theorem keepL_eq [Nontrivial A] (Γ : Ten → A) (hΓ : IsTen Γ) :
    turnsTen Γ ⊓ commWith (pairSum Γ) = keepJ.map (turnOf Γ) := by
  have hp : pairSum Γ = (2 : ℝ) • turnOf Γ cxJ := by
    rw [turnOf_cxJ Γ hΓ, smul_smul]
    norm_num
  ext X
  constructor
  · rintro ⟨⟨M, hM, rfl⟩, hC⟩
    refine ⟨M, ⟨hM, ?_⟩, rfl⟩
    rw [SetLike.mem_coe, mem_commWith, hp, mul_smul_comm, smul_mul_assoc] at hC
    have h1 : turnOf Γ M * turnOf Γ cxJ - turnOf Γ cxJ * turnOf Γ M = 0 := by
      have := smul_right_injective A (two_ne_zero : (2 : ℝ) ≠ 0) hC
      rw [this, sub_self]
    rw [turnOf_lie Γ hΓ M cxJ hM] at h1
    have h2 := turnOf_eq_zero Γ hΓ _ (cxJ_comm_skew M hM) h1
    rw [SetLike.mem_coe, mem_commWith]
    exact sub_eq_zero.mp h2
  · rintro ⟨M, ⟨hM, hJ⟩, rfl⟩
    refine ⟨⟨M, hM, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_commWith] at hJ
    have h1 : turnOf Γ M * turnOf Γ cxJ - turnOf Γ cxJ * turnOf Γ M = 0 := by
      rw [turnOf_lie Γ hΓ M cxJ hM, hJ, sub_self, map_zero]
    rw [SetLike.mem_coe, mem_commWith, hp, mul_smul_comm, smul_mul_assoc, sub_eq_zero.mp h1]

/-- **The rotations that keep the comparison: `u(5)`, dimension 25.** -/
theorem finrank_keepL [Nontrivial A] (Γ : Ten → A) (hΓ : IsTen Γ) :
    Module.finrank ℝ (turnsTen Γ ⊓ commWith (pairSum Γ) : Submodule ℝ A) = 25 := by
  have hinj : Function.Injective ((turnOf Γ).comp uFive) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro R hR
    have h0 := turnOf_eq_zero Γ hΓ (uFive R) (uFive_mem_skew R) hR
    exact uFive_injective (by rw [h0, map_zero])
  rw [keepL_eq Γ hΓ, ← range_uFive, ← LinearMap.range_comp, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_matrix]
  simp

end Turns

/-! ## The ten lines of a pair on `H ⊗ H ⊗ ℂ²` -/

section PairModel

theorem tenLine_isTen : IsTen tenLine := by
  intro x y
  rw [tenLine_clifford]
  split_ifs
  · rw [two_smul, two_smul]
  · rw [zero_smul]

theorem pairSum_tenLine : pairSum tenLine = I • ((L - 1) ⊗ₖ σ₃) := by
  rw [← comparison_as_turn, smul_smul, pairSum]
  simp

theorem commWith_I_smul {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℂ) :
    commWith (I • C) = commWith C := by
  ext Y
  rw [mem_commWith, mem_commWith, mul_smul_comm, smul_mul_assoc]
  exact ⟨fun h => smul_right_injective _ I_ne_zero h, fun h => by rw [h]⟩

/-- **On `H ⊗ H ⊗ ℂ²` the forty-five rotations of the ten lines of a pair span `so(10)`, dimension
45.** -/
theorem pair_turns_finrank : Module.finrank ℝ (turnsTen tenLine) = 45 :=
  finrank_turnsTen tenLine tenLine_isTen

/-- **The rotations that keep the comparison `(L − 1) ⊗ σ_z`: `u(5)`, dimension 25.** -/
theorem pair_keepL_finrank :
    Module.finrank ℝ (turnsTen tenLine ⊓ commWith ((L - 1) ⊗ₖ σ₃) : Submodule ℝ _) = 25 := by
  rw [← commWith_I_smul, ← pairSum_tenLine]
  exact finrank_keepL tenLine tenLine_isTen

theorem kron_neg' {m n p q : Type*} (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext i j
  simp [Matrix.kroneckerMap_apply]

theorem sub_kron' {m n p q : Type*} (A B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, sub_mul]

/-- The chirality `1 ⊗ 1 ⊗ σ_z`: `+1` on the two-spinor states, `−1` on the other half. -/
def chirality : Matrix (Two × Fin 2) (Two × Fin 2) ℂ := (1 : Matrix Two Two ℂ) ⊗ₖ σ₃

theorem σ₃_mul_σ₃ : σ₃ * σ₃ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₁_σ₃_anti : σ₁ * σ₃ = -(σ₃ * σ₁) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₂_σ₃_anti : σ₂ * σ₃ = -(σ₃ * σ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem chirality_sq : chirality * chirality = 1 := by
  rw [chirality, ← Matrix.mul_kronecker_mul, Matrix.one_mul, σ₃_mul_σ₃, Matrix.one_kronecker_one]

/-- Each of the ten lines exchanges the two halves. -/
theorem tenLine_chirality (x : Ten) : tenLine x * chirality = -(chirality * tenLine x) := by
  rcases x with a | a
  · simp only [tenLine, chirality]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      σ₁_σ₃_anti, kron_neg']
  · simp only [tenLine, chirality]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      σ₂_σ₃_anti, kron_neg']

/-- Every rotation keeps the two halves. -/
theorem turnOf_chirality (M : Matrix Ten Ten ℝ) :
    turnOf tenLine M * chirality = chirality * turnOf tenLine M := by
  rw [turnOf_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Matrix.mul_assoc, tenLine_chirality y, Matrix.mul_neg, ← Matrix.mul_assoc,
    tenLine_chirality x, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

theorem comparison_chirality :
    (L - 1) ⊗ₖ σ₃ = (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) * chirality := by
  rw [Matrix.sub_mul, chirality, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, sub_kron']

/-- **Keeping `L` on both halves is keeping the comparison `(L − 1) ⊗ σ_z`.** -/
theorem keepL_pair_eq :
    turnsTen tenLine ⊓ commWith (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      turnsTen tenLine ⊓ commWith ((L - 1) ⊗ₖ σ₃) := by
  ext X
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine and_congr_right fun hX => ?_
  obtain ⟨M, -, rfl⟩ := hX
  have hω := turnOf_chirality M
  set X := turnOf tenLine M
  set A := L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [mem_commWith, mem_commWith, comparison_chirality]
  constructor
  · intro h
    calc X * ((A - 1) * chirality) = X * (A * chirality) - X * chirality := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
      _ = A * (X * chirality) - X * chirality := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
      _ = A * (chirality * X) - chirality * X := by rw [hω]
      _ = (A - 1) * chirality * X := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc]
  · intro h
    have h2 : X * (A - 1) = (A - 1) * X := by
      calc X * (A - 1) = X * ((A - 1) * chirality) * chirality := by
            rw [Matrix.mul_assoc X, Matrix.mul_assoc, chirality_sq, Matrix.mul_one]
        _ = (A - 1) * chirality * X * chirality := by rw [h]
        _ = (A - 1) * X := by
            rw [Matrix.mul_assoc ((A - 1) * chirality) X chirality, hω, ← Matrix.mul_assoc,
              Matrix.mul_assoc (A - 1) chirality chirality, chirality_sq, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact sub_left_injective h2

/-- **The rotations of the ten lines of a pair that keep `L`: `u(5)`, dimension 25.** -/
theorem pair_keepL_finrank' :
    Module.finrank ℝ (turnsTen tenLine ⊓ commWith (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
      Submodule ℝ _) = 25 := by
  rw [keepL_pair_eq]
  exact pair_keepL_finrank

end PairModel

/-! ## The ten lines on the exterior algebra of five complex lines -/

section Fock

/-- The operators on `Λℂ⁵`, the thirty-two sets of five complex lines. -/
abbrev FockE := Module.End ℂ (Finset (Fin 5) → ℂ)

/-- **The ten lines on `Λℂ⁵`:** `Γ_t = ε_t + ι_t`, `Γ_{5+t} = i(ε_t − ι_t)`. -/
noncomputable def fockLine : Ten → FockE
  | Sum.inl t => εx t + ιx t
  | Sum.inr t => I • (εx t - ιx t)

theorem fockLine_isTen : IsTen fockLine := by
  have hee := fun a b : Fin 5 => εx_εx_add (R := ℂ) a b
  have hii := fun a b : Fin 5 => ιx_ιx_add (R := ℂ) a b
  have hei := fun a b : Fin 5 => εx_ιx_add (R := ℂ) a b
  intro x y
  rcases x with s | s <;> rcases y with t | t
  · simp only [fockLine, Sum.inl.injEq]
    calc (εx s + ιx s) * (εx t + ιx t) + (εx t + ιx t) * (εx s + ιx s)
        = (εx s * εx t + εx t * εx s) + (ιx s * ιx t + ιx t * ιx s) +
            (εx s * ιx t + ιx t * εx s) + (εx t * ιx s + ιx s * εx t) := by noncomm_ring
      _ = _ := by
        rw [hee, hii, hei, hei]
        by_cases h : s = t
        · subst h
          simp [two_smul]
        · simp [h, Ne.symm h]
  · simp only [fockLine, reduceCtorEq, ite_false, zero_smul]
    calc (εx s + ιx s) * (I • (εx t - ιx t)) + (I • (εx t - ιx t)) * (εx s + ιx s)
        = I • ((εx s * εx t + εx t * εx s) - (ιx s * ιx t + ιx t * ιx s) -
            (εx s * ιx t + ιx t * εx s) + (εx t * ιx s + ιx s * εx t)) := by
          simp only [mul_smul_comm, smul_mul_assoc, ← smul_add]
          congr 1
          simp only [mul_add, add_mul, mul_sub, sub_mul]
          abel
      _ = 0 := by
        rw [hee, hii, hei, hei]
        by_cases h : s = t
        · subst h
          simp
        · simp [h, Ne.symm h]
  · simp only [fockLine, reduceCtorEq, ite_false, zero_smul]
    calc (I • (εx s - ιx s)) * (εx t + ιx t) + (εx t + ιx t) * (I • (εx s - ιx s))
        = I • ((εx s * εx t + εx t * εx s) - (ιx s * ιx t + ιx t * ιx s) +
            (εx s * ιx t + ιx t * εx s) - (εx t * ιx s + ιx s * εx t)) := by
          simp only [mul_smul_comm, smul_mul_assoc, ← smul_add]
          congr 1
          simp only [mul_add, add_mul, mul_sub, sub_mul]
          abel
      _ = 0 := by
        rw [hee, hii, hei, hei]
        by_cases h : s = t
        · subst h
          simp
        · simp [h, Ne.symm h]
  · simp only [fockLine, Sum.inr.injEq]
    calc (I • (εx s - ιx s)) * (I • (εx t - ιx t)) + (I • (εx t - ιx t)) * (I • (εx s - ιx s))
        = (I * I) • ((εx s * εx t + εx t * εx s) + (ιx s * ιx t + ιx t * ιx s) -
            (εx s * ιx t + ιx t * εx s) - (εx t * ιx s + ιx s * εx t)) := by
          simp only [mul_smul_comm, smul_mul_assoc, smul_smul, ← smul_add]
          congr 1
          simp only [mul_sub, sub_mul]
          abel
      _ = _ := by
        rw [hee, hii, hei, hei, I_mul_I]
        by_cases h : s = t
        · subst h
          simp only [ite_true]
          module
        · simp [h, Ne.symm h]

/-- The complex coefficient `Z_st = A_st + iB_st` of the rotation `uFive R`. -/
noncomputable def zc (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : ℂ :=
  (skA R s t : ℂ) + I * (syB R s t : ℂ)

theorem skA_swap (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : skA R t s = -skA R s t := by
  have := congrFun (congrFun (skA_transpose R) s) t
  simpa using this

theorem syB_swap (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : syB R t s = syB R s t := by
  have := congrFun (congrFun (syB_transpose R) s) t
  simpa using this

theorem skA_diag (R : Matrix (Fin 5) (Fin 5) ℝ) (t : Fin 5) : skA R t t = 0 := by
  simp [skA]

theorem syB_diag (R : Matrix (Fin 5) (Fin 5) ℝ) (t : Fin 5) : syB R t t = R t t := by
  simp [syB]

theorem zc_diag (R : Matrix (Fin 5) (Fin 5) ℝ) (t : Fin 5) : zc R t t = I * (R t t : ℂ) := by
  rw [zc, skA_diag, syB_diag]
  simp

/-- `ι_s ε_t = δ_st − ε_t ι_s`, summed with any coefficients. -/
theorem sum_ιε (c : Fin 5 → Fin 5 → ℂ) :
    ∑ s, ∑ t, c s t • (ιx s * εx t : FockE) =
      (∑ s, c s s) • (1 : FockE) - ∑ s, ∑ t, c t s • (εx s * ιx t : FockE) := by
  have h : ∀ s t : Fin 5, (ιx s * εx t : FockE) = (if t = s then 1 else 0) - εx t * ιx s :=
    fun s t => eq_sub_of_add_eq' (εx_ιx_add (R := ℂ) t s)
  simp only [h, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun s t => c s t • (εx t * ιx s : FockE))]

/-- One term of `ρ(uFive R)`: `¼(A a_sa_t − B a_sb_t + B b_sa_t + A b_sb_t)`. -/
theorem fock_term (a b : ℝ) (s t : Fin 5) :
    ((1 / 4 : ℝ) * a) • (fockLine (Sum.inl s) * fockLine (Sum.inl t)) +
        ((1 / 4 : ℝ) * -b) • (fockLine (Sum.inl s) * fockLine (Sum.inr t)) +
      (((1 / 4 : ℝ) * b) • (fockLine (Sum.inr s) * fockLine (Sum.inl t)) +
        ((1 / 4 : ℝ) * a) • (fockLine (Sum.inr s) * fockLine (Sum.inr t))) =
      ((a / 2 : ℂ) + (b / 2 : ℂ) * I) • (εx s * ιx t : FockE) +
        ((a / 2 : ℂ) - (b / 2 : ℂ) * I) • (ιx s * εx t : FockE) := by
  simp only [fockLine]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_sub, I_mul_I]
  module

/-- **The normal form of a rotation of five complex lines:**
`ρ(uFive R) = Σ_{s,t} Z_st ε_sι_t − ½ tr Z`, `Z = A + iB`: on `Λℂ⁵`, `u(5)` acts as on the
exterior powers, twisted by `det^{−1/2}`. -/
theorem fock_normal (R : Matrix (Fin 5) (Fin 5) ℝ) :
    turnOf fockLine (uFive R) =
      ∑ s, ∑ t, zc R s t • (εx s * ιx t : FockE) - ((1 / 2 : ℂ) * ∑ t, zc R t t) • (1 : FockE) := by
  have e1 : turnOf fockLine (uFive R) = ∑ s, ∑ t,
      ((((skA R s t : ℂ) / 2 + (syB R s t : ℂ) / 2 * I) • (εx s * ιx t : FockE)) +
        (((skA R s t : ℂ) / 2 - (syB R s t : ℂ) / 2 * I) • (ιx s * εx t : FockE))) := by
    rw [turnOf_apply, Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, uFive_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.neg_apply]
    simp only [← fock_term, Finset.sum_add_distrib]
  rw [e1]
  simp only [Finset.sum_add_distrib]
  rw [sum_ιε (fun s t => (skA R s t : ℂ) / 2 - (syB R s t : ℂ) / 2 * I)]
  have hc : ∀ s t, ((skA R s t : ℂ) / 2 + (syB R s t : ℂ) / 2 * I) -
      ((skA R t s : ℂ) / 2 - (syB R t s : ℂ) / 2 * I) = zc R s t := by
    intro s t
    rw [skA_swap R s t, syB_swap R s t, zc]
    push_cast
    ring
  have hd : ∑ s, ((skA R s s : ℂ) / 2 - (syB R s s : ℂ) / 2 * I) =
      -((1 / 2 : ℂ) * ∑ t, zc R t t) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [zc, skA_diag]
    push_cast
    ring
  have hsum : ∑ s, ∑ t, ((skA R s t : ℂ) / 2 + (syB R s t : ℂ) / 2 * I) • (εx s * ιx t : FockE) -
      ∑ s, ∑ t, ((skA R t s : ℂ) / 2 - (syB R t s : ℂ) / 2 * I) • (εx s * ιx t : FockE) =
      ∑ s, ∑ t, zc R s t • (εx s * ιx t : FockE) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact (sub_smul _ _ _).symm.trans (congrArg (fun c => c • (εx s * ιx t : FockE)) (hc s t))
  rw [hd, ← hsum]
  module

/-! ### What `ε_sι_t` does to a set -/

theorem epsIota_self {T : Finset (Fin 5)} {t : Fin 5} (ht : t ∈ T) :
    (εx t * ιx t : FockE) (Pi.single T 1) = Pi.single T 1 := by
  rw [Module.End.mul_apply, ιx_single, ite_eq_left ht, map_smul, εx_single,
    ite_eq_right (Finset.notMem_erase t T), smul_smul, extSign_mul_self, one_smul,
    Finset.insert_erase ht]

theorem epsIota_out {T : Finset (Fin 5)} (s : Fin 5) {t : Fin 5} (ht : t ∉ T) :
    (εx s * ιx t : FockE) (Pi.single T 1) = 0 := by
  rw [Module.End.mul_apply, ιx_single, ite_eq_right ht, map_zero]

theorem epsIota_in {T : Finset (Fin 5)} {s t : Fin 5} (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t) :
    (εx s * ιx t : FockE) (Pi.single T 1) = 0 := by
  rw [Module.End.mul_apply, ιx_single, ite_eq_left ht, map_smul, εx_single,
    ite_eq_left (Finset.mem_erase.mpr ⟨hst, hs⟩), smul_zero]

theorem epsIota_transition {T : Finset (Fin 5)} {s t : Fin 5} (hs : s ∉ T) (ht : t ∈ T) :
    (εx s * ιx t : FockE) (Pi.single T 1) =
      (extSign (R := ℂ) t (T.erase t) * extSign (R := ℂ) s (T.erase t)) •
        Pi.single (insert s (T.erase t)) 1 := by
  rw [Module.End.mul_apply, ιx_single, ite_eq_left ht, map_smul, εx_single,
    ite_eq_right (fun h => hs (Finset.mem_of_mem_erase h)), smul_smul]

/-! ### The three quantities kept -/

/-- `Ω = f_∅`: the two-spinor state of a moment with itself, `Λ⁰`. -/
def vacF : Finset (Fin 5) → ℂ := Pi.single ∅ 1

/-- `N_F = N_h + N_k`, the number of lines of the plane `F = {h, k}` (`h = 3`, `k = 4`). -/
noncomputable def planeN : FockE := εx 3 * ιx 3 + εx 4 * ιx 4

/-- `ℓ_h = f_{C ∪ {k}}`: the two-spinor state with `N_h = 0`, `N_k = 1`, `N_C = 3` (`C = {0, 1, 2}`). -/
def lastDirectionRelVec : Finset (Fin 5) → ℂ := Pi.single {0, 1, 2, 4} 1

/-- The real operators that annihilate `v`. -/
def annih (v : Finset (Fin 5) → ℂ) : Submodule ℝ FockE where
  carrier := {X | X v = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_apply, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' c X hX := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_apply, hX, smul_zero]

theorem mem_annih (v : Finset (Fin 5) → ℂ) (X : FockE) : X ∈ annih v ↔ X v = 0 := Iff.rfl

theorem trace_zc (R : Matrix (Fin 5) (Fin 5) ℝ) : ∑ t, zc R t t = I * (R.trace : ℂ) := by
  simp only [zc_diag, Matrix.trace, Matrix.diag, ← Finset.mul_sum]
  push_cast
  rfl

/-- **On `Ω`, a rotation of `u(5)` acts by `−½ tr Z`:** `ρ(uFive R) Ω = −(i/2) tr R · Ω`. -/
theorem turn_vac (R : Matrix (Fin 5) (Fin 5) ℝ) :
    turnOf fockLine (uFive R) vacF = (-(I / 2 * (R.trace : ℂ))) • vacF := by
  rw [fock_normal, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.sum_apply]
  have h0 : ∀ s t : Fin 5, (εx s * ιx t : FockE) vacF = 0 := fun s t => by
    rw [Module.End.mul_apply, vacF, ιx_vac, map_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_zero, Finset.sum_const_zero,
    zero_sub, trace_zc, ← neg_smul]
  congr 1
  ring

theorem vacF_ne : vacF ≠ 0 := by
  intro h
  have := congrFun h ∅
  simp [vacF] at this

/-- **Keeping `Ω` is `tr R = 0`** (`su(5)`). -/
theorem turn_vac_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    turnOf fockLine (uFive R) vacF = 0 ↔ R.trace = 0 := by
  rw [turn_vac, smul_eq_zero, or_iff_left vacF_ne, neg_eq_zero, mul_eq_zero, or_iff_right
    (div_ne_zero I_ne_zero two_ne_zero)]
  exact_mod_cast Iff.rfl

/-! ### Keeping the plane -/

/-- `ρ` of a diagonal pairing: `ρ([[0, D], [−D, 0]]) = ½ Σ_t d_t Γ_tΓ_{5+t}`. -/
theorem turnOf_pairDiag {A : Type*} [Ring A] [Algebra ℝ A] (Γ : Ten → A) (hΓ : IsTen Γ)
    (d : Fin 5 → ℝ) :
    turnOf Γ (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) =
      (1 / 2 : ℝ) • ∑ t, d t • (Γ (Sum.inl t) * Γ (Sum.inr t)) := by
  rw [turnOf_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.diagonal_apply,
    Matrix.neg_apply, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, add_zero, mul_ite,
    mul_neg, neg_smul, Finset.sum_neg_distrib, ite_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.smul_sum, smul_smul]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [anti_of_ne Γ hΓ Sum.inl_ne_inr, smul_neg, sub_neg_eq_add, ← add_smul]
  congr 1
  ring

/-- `N_t = ½ + (i/2) Γ_tΓ_{5+t}`. -/
theorem numOp_eq (t : Fin 5) :
    (εx t * ιx t : FockE) =
      (1 / 2 : ℂ) • 1 + (I / 2) • (fockLine (Sum.inl t) * fockLine (Sum.inr t)) := by
  have h1 : (εx t * ιx t + ιx t * εx t : FockE) = 1 := by
    rw [εx_ιx_add (R := ℂ) t t, ite_eq_left rfl]
  have hee : (εx t * εx t : FockE) = 0 := εx_mul_self t
  have hii : (ιx t * ιx t : FockE) = 0 := ιx_mul_self t
  have e : fockLine (Sum.inl t) * fockLine (Sum.inr t) =
      I • (εx t * εx t - εx t * ιx t + ιx t * εx t - ιx t * ιx t : FockE) := by
    simp only [fockLine, mul_smul_comm, mul_sub, add_mul]
    congr 1
    abel
  have h2 : (ιx t * εx t : FockE) = 1 - εx t * ιx t := eq_sub_of_add_eq' h1
  rw [e, hee, hii, h2, smul_smul]
  have : I / 2 * I = -(1 / 2 : ℂ) := by
    rw [div_mul_eq_mul_div, I_mul_I]
    ring
  rw [this]
  module

/-- `Γ_tΓ_{5+t} = i(1 − 2N_t)`. -/
theorem lineLine_eq (t : Fin 5) :
    fockLine (Sum.inl t) * fockLine (Sum.inr t) = I • (1 - (2 : ℂ) • (εx t * ιx t : FockE)) := by
  have h1 : (εx t * ιx t + ιx t * εx t : FockE) = 1 := by
    rw [εx_ιx_add (R := ℂ) t t, ite_eq_left rfl]
  have hee : (εx t * εx t : FockE) = 0 := εx_mul_self t
  have hii : (ιx t * ιx t : FockE) = 0 := ιx_mul_self t
  have h2 : (ιx t * εx t : FockE) = 1 - εx t * ιx t := eq_sub_of_add_eq' h1
  have e : fockLine (Sum.inl t) * fockLine (Sum.inr t) =
      I • (εx t * εx t - εx t * ιx t + ιx t * εx t - ιx t * ιx t : FockE) := by
    simp only [fockLine, mul_smul_comm, mul_sub, add_mul]
    congr 1
    abel
  rw [e, hee, hii, h2]
  congr 1
  module

/-- **On `Λℂ⁵` the comparison less one is `5 − 2N`:** `−i Σ_t Γ_tΓ_{5+t} = 5 − 2N`, `N` the
number of lines (Proposition 10's `L − 1 = 5 − 2N`). -/
theorem fock_comparison :
    (-I) • pairSum fockLine = (5 : ℂ) • (1 : FockE) - (2 : ℂ) • (Nx : FockE) := by
  have hI : -I * I = 1 := by rw [neg_mul, I_mul_I, neg_neg]
  rw [pairSum, Finset.smul_sum]
  simp only [lineLine_eq, smul_smul, hI, one_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
    Nx_eq_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

/-- The plane `F = {3, 4}`: `d_t = 1` on the plane, `0` on the three outside lines. -/
def dF (t : Fin 5) : ℝ := if 3 ≤ t then 1 else 0

/-- The complex structure of the plane alone. -/
def planeJ : Matrix Ten Ten ℝ := Matrix.fromBlocks 0 (Matrix.diagonal dF) (-Matrix.diagonal dF) 0

theorem planeJ_transpose : planeJᵀ = -planeJ := by
  rw [planeJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp

/-- **`N_F = 1 + i ρ(J_F)`.** -/
theorem planeN_eq : planeN = 1 + I • turnOf fockLine planeJ := by
  rw [planeJ, turnOf_pairDiag fockLine fockLine_isTen, planeN, numOp_eq, numOp_eq]
  simp only [Fin.sum_univ_five, dF]
  norm_num
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

theorem comm_skew (M N : Matrix Ten Ten ℝ) (hM : Mᵀ = -M) (hN : Nᵀ = -N) :
    (M * N - N * M)ᵀ = -(M * N - N * M) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hM, hN]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_sub]

/-- **A rotation keeps `N_F` exactly when its matrix commutes with the plane's structure.** -/
theorem plane_comm_iff (M : Matrix Ten Ten ℝ) (hM : Mᵀ = -M) :
    turnOf fockLine M * planeN = planeN * turnOf fockLine M ↔ M * planeJ = planeJ * M := by
  have hlie := turnOf_lie fockLine fockLine_isTen M planeJ hM
  rw [planeN_eq, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  constructor
  · intro h
    have h1 : I • (turnOf fockLine M * turnOf fockLine planeJ) =
        I • (turnOf fockLine planeJ * turnOf fockLine M) := add_left_cancel h
    have h2 := smul_right_injective FockE I_ne_zero h1
    have h3 : turnOf fockLine (M * planeJ - planeJ * M) = 0 := by rw [← hlie, h2, sub_self]
    exact sub_eq_zero.mp (turnOf_eq_zero fockLine fockLine_isTen _
      (comm_skew M planeJ hM planeJ_transpose) h3)
  · intro h
    have h3 : turnOf fockLine M * turnOf fockLine planeJ =
        turnOf fockLine planeJ * turnOf fockLine M := by
      rw [← sub_eq_zero, hlie, h, sub_self, map_zero]
    rw [h3]

/-- The pairs of a line of the plane with a line outside it. -/
def crossP (p : Fin 5 × Fin 5) : Prop := (p.1 < 3 ∧ 3 ≤ p.2) ∨ (3 ≤ p.1 ∧ p.2 < 3)

instance : DecidablePred crossP := fun p => by unfold crossP; infer_instance

theorem dF_eq_iff : ∀ s t : Fin 5, dF s = dF t ↔ ¬crossP (s, t) := by
  intro s t
  fin_cases s <;> fin_cases t <;> simp [dF, crossP]

theorem crossP_symm {s t : Fin 5} (h : crossP (s, t)) : crossP (t, s) := by
  unfold crossP at *
  tauto

/-- **The rotations of five complex lines that keep `N_F`: the block-diagonal ones.** -/
theorem uFive_plane_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    uFive R * planeJ = planeJ * uFive R ↔ ∀ s t, crossP (s, t) → R s t = 0 := by
  rw [uFive_apply, planeJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, neg_zero]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨hB, hA, -, -⟩ s t hst
    have hd : dF s ≠ dF t := fun h => (dF_eq_iff s t).mp h hst
    have eA := congrFun (congrFun hA s) t
    have eB := congrFun (congrFun hB s) t
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at eA eB
    have hA0 : skA R s t = 0 := by
      have : skA R s t * (dF t - dF s) = 0 := by rw [mul_sub, eA]; ring
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hd))
    have hB0 : syB R s t = 0 := by
      have : syB R s t * (dF t - dF s) = 0 := by rw [mul_sub, eB]; ring
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hd))
    rcases lt_or_ge s t with h | h
    · simpa [skA, h] using hA0
    · simpa [syB, h] using hB0
  · intro hR
    have hz : ∀ s t, crossP (s, t) → skA R s t = 0 ∧ syB R s t = 0 := by
      intro s t hst
      have h1 := hR s t hst
      have h2 := hR t s (crossP_symm hst)
      simp only [skA, syB, Matrix.of_apply, h1, h2, neg_zero]
      constructor
      · split_ifs <;> rfl
      · split_ifs <;> rfl
    have key : ∀ (X : Matrix (Fin 5) (Fin 5) ℝ), (∀ s t, crossP (s, t) → X s t = 0) →
        X * Matrix.diagonal dF = Matrix.diagonal dF * X := by
      intro X hX
      ext s t
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hst : crossP (s, t)
      · rw [hX s t hst, zero_mul, mul_zero]
      · rw [(dF_eq_iff s t).mpr hst, mul_comm]
    refine ⟨key _ fun s t h => (hz s t h).2, key _ fun s t h => (hz s t h).1, ?_,
      key _ fun s t h => (hz s t h).2⟩
    rw [key _ fun s t h => (hz s t h).1]

/-! ### Keeping the last-step direction's two-spinor state -/

theorem zc_cross {R : Matrix (Fin 5) (Fin 5) ℝ} (hR : ∀ s t, crossP (s, t) → R s t = 0)
    {s t : Fin 5} (hst : crossP (s, t)) : zc R s t = 0 := by
  have h1 := hR s t hst
  have h2 := hR t s (crossP_symm hst)
  have hA : skA R s t = 0 := by
    simp only [skA, Matrix.of_apply, h1, h2, neg_zero]
    split_ifs <;> rfl
  have hB : syB R s t = 0 := by
    simp only [syB, Matrix.of_apply, h1, h2]
    split_ifs <;> rfl
  rw [zc, hA, hB]
  simp

/-- The two-spinor state `f_{0123}` reached from `ℓ_h` by moving the line `k = 4` to the last-step direction `h = 3`. -/
def movedVec : Finset (Fin 5) → ℂ := Pi.single {0, 1, 2, 3} 1

theorem lastDirection_term (R : Matrix (Fin 5) (Fin 5) ℝ) (hR : ∀ s t, crossP (s, t) → R s t = 0)
    (s t : Fin 5) :
    zc R s t • (εx s * ιx t : FockE) lastDirectionRelVec =
      (if s = t ∧ t ≠ 3 then zc R s t • lastDirectionRelVec else 0) +
        (if s = 3 ∧ t = 4 then zc R 3 4 • movedVec else 0) := by
  have hc : ∀ s t : Fin 5, crossP (s, t) → zc R s t = 0 := fun s t h => zc_cross hR h
  have hset : insert (3 : Fin 5) (({0, 1, 2, 4} : Finset (Fin 5)).erase 4) = {0, 1, 2, 3} := by
    decide
  fin_cases s <;> fin_cases t <;>
    simp (disch := decide) only [lastDirectionRelVec, movedVec, epsIota_self, epsIota_out, epsIota_in,
      epsIota_transition, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    simp (disch := decide) [hc, extSign, hset]

/-- **A block-diagonal rotation on `ℓ_h`:**
`ρ(uFive R) ℓ_h = (Z₀₀ + Z₁₁ + Z₂₂ + Z₄₄ − ½ tr Z) ℓ_h + Z₃₄ f_{0123}`. -/
theorem turn_lastDirection (R : Matrix (Fin 5) (Fin 5) ℝ) (hR : ∀ s t, crossP (s, t) → R s t = 0) :
    turnOf fockLine (uFive R) lastDirectionRelVec =
      (zc R 0 0 + zc R 1 1 + zc R 2 2 + zc R 4 4 - (1 / 2 : ℂ) * ∑ t, zc R t t) • lastDirectionRelVec +
        zc R 3 4 • movedVec := by
  rw [fock_normal, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, lastDirection_term R hR, Finset.sum_add_distrib]
  simp only [Fin.sum_univ_five, Fin.isValue]
  simp (disch := decide) only [and_true, and_false, ne_eq, ite_true,
    ite_false, Fin.reduceEq, not_false_eq_true, not_true_eq_false, add_zero, zero_add]
  rw [sub_smul]
  module

theorem lastDirectionRelVec_at : lastDirectionRelVec {0, 1, 2, 4} = 1 ∧ movedVec {0, 1, 2, 4} = 0 ∧
    lastDirectionRelVec {0, 1, 2, 3} = 0 ∧ movedVec {0, 1, 2, 3} = 1 := by
  simp +decide [lastDirectionRelVec, movedVec]

/-- **Keeping `ℓ_h`:** for a rotation that keeps `Ω` and `N_F`, `ρ(uFive R) ℓ_h = 0` exactly when
`Z₃₃ = 0` and `Z₃₄ = 0`, i.e. `R₃₃ = R₃₄ = R₄₃ = 0`. -/
theorem turn_lastDirection_iff (R : Matrix (Fin 5) (Fin 5) ℝ) (htr : R.trace = 0)
    (hR : ∀ s t, crossP (s, t) → R s t = 0) :
    turnOf fockLine (uFive R) lastDirectionRelVec = 0 ↔ R 3 3 = 0 ∧ R 3 4 = 0 ∧ R 4 3 = 0 := by
  have hsum : ∑ t, zc R t t = 0 := by rw [trace_zc, htr]; simp
  have htr' : R 0 0 + R 1 1 + R 2 2 + R 3 3 + R 4 4 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_five] using htr
  have hdiag : zc R 0 0 + zc R 1 1 + zc R 2 2 + zc R 4 4 = -(I * (R 3 3 : ℂ)) := by
    simp only [zc_diag]
    have : (R 0 0 : ℂ) + R 1 1 + R 2 2 + R 3 3 + R 4 4 = 0 := by exact_mod_cast htr'
    linear_combination I * this
  have h34 : zc R 3 4 = (R 3 4 : ℂ) + I * (R 4 3 : ℂ) := by
    simp [zc, skA, syB]
  rw [turn_lastDirection R hR, hsum, mul_zero, sub_zero, hdiag, h34]
  obtain ⟨a1, a2, a3, a4⟩ := lastDirectionRelVec_at
  constructor
  · intro h
    have e1 := congrFun h {0, 1, 2, 4}
    have e2 := congrFun h {0, 1, 2, 3}
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, a1, a2, a3, a4, mul_one, mul_zero,
      add_zero, zero_add, Pi.zero_apply] at e1 e2
    have h33 : (R 3 3 : ℂ) = 0 := by
      have := neg_eq_zero.mp e1
      exact (mul_eq_zero.mp this).resolve_left I_ne_zero
    have hre : R 3 4 = 0 := by simpa using congrArg Complex.re e2
    have him : R 4 3 = 0 := by simpa using congrArg Complex.im e2
    exact ⟨by exact_mod_cast h33, hre, him⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    simp

/-! ### The vector form of the chain: real `5 × 5` matrices with entries set to zero -/

/-- The trace and the entries `P` of a real `5 × 5` matrix. -/
def kerP (P : Fin 5 × Fin 5 → Prop) [DecidablePred P] :
    Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ × ({p : Fin 5 × Fin 5 // P p} → ℝ) where
  toFun R := (R.trace, fun p => R p.1.1 p.1.2)
  map_add' R R' := by
    refine Prod.ext ?_ ?_
    · simp
    · funext p
      simp
  map_smul' c R := by
    refine Prod.ext ?_ ?_
    · simp
    · funext p
      simp

theorem mem_ker_kerP (P : Fin 5 × Fin 5 → Prop) [DecidablePred P] (R : Matrix (Fin 5) (Fin 5) ℝ) :
    R ∈ LinearMap.ker (kerP P) ↔ R.trace = 0 ∧ ∀ p, P p → R p.1 p.2 = 0 := by
  rw [LinearMap.mem_ker]
  change (R.trace, fun p : {p : Fin 5 × Fin 5 // P p} => R p.1.1 p.1.2) = 0 ↔ _
  rw [Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.zero_apply, Subtype.forall]

theorem kerP_surjective (P : Fin 5 × Fin 5 → Prop) [DecidablePred P] (h00 : ¬P (0, 0)) :
    Function.Surjective (kerP P) := by
  rintro ⟨a, w⟩
  refine ⟨(a - ∑ p, w p * if p.1.1 = p.1.2 then 1 else 0) • Matrix.single 0 0 1 +
    ∑ p, w p • Matrix.single p.1.1 p.1.2 1, ?_⟩
  refine Prod.ext ?_ ?_
  · change Matrix.trace ((a - ∑ p, w p * if p.1.1 = p.1.2 then 1 else 0) •
      Matrix.single (0 : Fin 5) (0 : Fin 5) (1 : ℝ) + ∑ p, w p • Matrix.single p.1.1 p.1.2 1) = a
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul]
    have ht : ∀ i j : Fin 5, Matrix.trace (Matrix.single i j (1 : ℝ)) = if i = j then 1 else 0 := by
      intro i j
      rw [Matrix.trace, Finset.sum_eq_single i]
      · simp only [Matrix.diag, Matrix.single_apply, true_and]
        by_cases h : i = j
        · simp [h]
        · simp [h, Ne.symm h]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    simp only [ht]
    simp
  · funext q
    change ((a - ∑ p, w p * if p.1.1 = p.1.2 then 1 else 0) • Matrix.single 0 0 1 +
      ∑ p, w p • Matrix.single p.1.1 p.1.2 1 : Matrix (Fin 5) (Fin 5) ℝ) q.1.1 q.1.2 = w q
    have hq : q.1 ≠ (0, 0) := fun h => h00 (h ▸ q.2)
    have h0 : ¬((0 : Fin 5) = q.1.1 ∧ (0 : Fin 5) = q.1.2) := fun h =>
      hq (Prod.ext h.1.symm h.2.symm)
    have h1 : ((a - ∑ p, w p * if p.1.1 = p.1.2 then 1 else 0) •
        Matrix.single (0 : Fin 5) (0 : Fin 5) (1 : ℝ)) q.1.1 q.1.2 = 0 := by
      rw [Matrix.smul_apply, Matrix.single_apply, ite_eq_right h0, smul_zero]
    have h2 : (∑ p, w p • Matrix.single p.1.1 p.1.2 (1 : ℝ)) q.1.1 q.1.2 = w q := by
      rw [Matrix.sum_apply, Finset.sum_eq_single q]
      · simp
      · intro p _ hp
        have : ¬(p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun h => hp (Subtype.ext (Prod.ext h.1 h.2))
        simp [this]
      · simp
    rw [Matrix.add_apply, h1, h2, zero_add]

theorem finrank_ker_kerP (P : Fin 5 × Fin 5 → Prop) [DecidablePred P] (h00 : ¬P (0, 0)) :
    Module.finrank ℝ (LinearMap.ker (kerP P)) + (1 + Fintype.card {p : Fin 5 × Fin 5 // P p}) =
      25 := by
  have h := LinearMap.finrank_range_add_finrank_ker (kerP P)
  rw [LinearMap.range_eq_top.mpr (kerP_surjective P h00), finrank_top, Module.finrank_prod,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card, Module.finrank_matrix] at h
  simp at h
  omega

/-- No entry set to zero: only the trace (`su(5)`). -/
def singletP (_ : Fin 5 × Fin 5) : Prop := False

instance : DecidablePred singletP := fun _ => isFalse id

/-- The plane's lines against the outside, and the last-step direction's diagonal entry and its pair with `k`. -/
def lastDirectionP (p : Fin 5 × Fin 5) : Prop := crossP p ∨ p = (3, 3) ∨ p = (3, 4) ∨ p = (4, 3)

instance : DecidablePred lastDirectionP := fun p => by unfold lastDirectionP; infer_instance

theorem card_singletP : Fintype.card {p : Fin 5 × Fin 5 // singletP p} = 0 := by decide

theorem card_crossP : Fintype.card {p : Fin 5 × Fin 5 // crossP p} = 12 := by decide

theorem card_lastDirectionP : Fintype.card {p : Fin 5 × Fin 5 // lastDirectionP p} = 15 := by decide

theorem finrank_su5 : Module.finrank ℝ (LinearMap.ker (kerP singletP)) = 24 := by
  have := finrank_ker_kerP singletP id
  rw [card_singletP] at this
  omega

theorem finrank_plane5 : Module.finrank ℝ (LinearMap.ker (kerP crossP)) = 12 := by
  have := finrank_ker_kerP crossP (by decide)
  rw [card_crossP] at this
  omega

theorem finrank_lastDirection5 : Module.finrank ℝ (LinearMap.ker (kerP lastDirectionP)) = 9 := by
  have := finrank_ker_kerP lastDirectionP (by decide)
  rw [card_lastDirectionP] at this
  omega

/-! ### The chain on the spinors: 45, 25, 24, 12, 9 -/

/-- The rotations of the ten lines on `Λℂ⁵` that keep the comparison `L`. -/
noncomputable def keepLF : Submodule ℝ FockE := turnsTen fockLine ⊓ commWith (pairSum fockLine)

/-- … that keep also `Ω`. -/
noncomputable def keepVacF : Submodule ℝ FockE := keepLF ⊓ annih vacF

/-- … that keep also `N_F`. -/
noncomputable def keepPlaneF : Submodule ℝ FockE := keepVacF ⊓ commWith planeN

/-- … that keep also `ℓ_h`. -/
noncomputable def keepLastDirectionF : Submodule ℝ FockE := keepPlaneF ⊓ annih lastDirectionRelVec

theorem fockTurn_injective : Function.Injective ((turnOf fockLine).comp uFive) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro R hR
  have h0 := turnOf_eq_zero fockLine fockLine_isTen (uFive R) (uFive_mem_skew R) hR
  exact uFive_injective (by rw [h0, map_zero])

theorem mem_keepLF (X : FockE) : X ∈ keepLF ↔ ∃ R, turnOf fockLine (uFive R) = X := by
  rw [keepLF, keepL_eq fockLine fockLine_isTen, ← range_uFive, ← LinearMap.range_comp]
  rfl

theorem keepVacF_eq :
    keepVacF = (LinearMap.ker (kerP singletP)).map ((turnOf fockLine).comp uFive) := by
  ext X
  rw [keepVacF, Submodule.mem_inf, mem_keepLF, mem_annih, Submodule.mem_map]
  constructor
  · rintro ⟨⟨R, rfl⟩, hΩ⟩
    refine ⟨R, ?_, rfl⟩
    rw [mem_ker_kerP]
    exact ⟨(turn_vac_iff R).mp hΩ, fun _ h => h.elim⟩
  · rintro ⟨R, hR, rfl⟩
    rw [mem_ker_kerP] at hR
    exact ⟨⟨R, rfl⟩, (turn_vac_iff R).mpr hR.1⟩

theorem keepPlaneF_eq :
    keepPlaneF = (LinearMap.ker (kerP crossP)).map ((turnOf fockLine).comp uFive) := by
  ext X
  rw [keepPlaneF, Submodule.mem_inf, keepVacF_eq, Submodule.mem_map, Submodule.mem_map,
    mem_commWith]
  constructor
  · rintro ⟨⟨R, hR, rfl⟩, hF⟩
    refine ⟨R, ?_, rfl⟩
    rw [mem_ker_kerP] at hR ⊢
    have := (plane_comm_iff (uFive R) (uFive_mem_skew R)).mp hF
    exact ⟨hR.1, fun p hp => (uFive_plane_iff R).mp this p.1 p.2 hp⟩
  · rintro ⟨R, hR, rfl⟩
    rw [mem_ker_kerP] at hR
    refine ⟨⟨R, (mem_ker_kerP _ R).mpr ⟨hR.1, fun _ h => h.elim⟩, rfl⟩, ?_⟩
    exact (plane_comm_iff (uFive R) (uFive_mem_skew R)).mpr
      ((uFive_plane_iff R).mpr fun s t h => hR.2 (s, t) h)

theorem keepLastDirectionF_eq :
    keepLastDirectionF = (LinearMap.ker (kerP lastDirectionP)).map ((turnOf fockLine).comp uFive) := by
  ext X
  rw [keepLastDirectionF, Submodule.mem_inf, keepPlaneF_eq, Submodule.mem_map, Submodule.mem_map,
    mem_annih]
  constructor
  · rintro ⟨⟨R, hR, rfl⟩, hh⟩
    refine ⟨R, ?_, rfl⟩
    rw [mem_ker_kerP] at hR ⊢
    have hc : ∀ s t, crossP (s, t) → R s t = 0 := fun s t h => hR.2 (s, t) h
    obtain ⟨h1, h2, h3⟩ := (turn_lastDirection_iff R hR.1 hc).mp hh
    refine ⟨hR.1, fun p hp => ?_⟩
    rcases hp with hp | rfl | rfl | rfl
    · exact hR.2 p hp
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨R, hR, rfl⟩
    rw [mem_ker_kerP] at hR
    have hc : ∀ s t, crossP (s, t) → R s t = 0 := fun s t h => hR.2 (s, t) (Or.inl h)
    refine ⟨⟨R, (mem_ker_kerP _ R).mpr ⟨hR.1, fun p hp => hc p.1 p.2 hp⟩, rfl⟩, ?_⟩
    exact (turn_lastDirection_iff R hR.1 hc).mpr
      ⟨hR.2 (3, 3) (Or.inr (Or.inl rfl)), hR.2 (3, 4) (Or.inr (Or.inr (Or.inl rfl))),
        hR.2 (4, 3) (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- **Proposition 46, the chain of what the rotations keep, on the spinors of the ten lines:**
`so(10)` 45, keeping `L` 25 (`u(5)`), keeping also `Ω` 24 (`su(5)`), keeping also `N_F` 12
(`s(u(3) ⊕ u(2))`), keeping also `ℓ_h` 9 (`su(3) ⊕ u(1)`). -/
theorem turns_chain :
    Module.finrank ℝ (turnsTen fockLine) = 45 ∧ Module.finrank ℝ keepLF = 25 ∧
      Module.finrank ℝ keepVacF = 24 ∧ Module.finrank ℝ keepPlaneF = 12 ∧
        Module.finrank ℝ keepLastDirectionF = 9 := by
  have e : ∀ S : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ),
      Module.finrank ℝ (S.map ((turnOf fockLine).comp uFive)) = Module.finrank ℝ S := fun S =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ fockTurn_injective S)).symm
  refine ⟨finrank_turnsTen fockLine fockLine_isTen, finrank_keepL fockLine fockLine_isTen, ?_, ?_,
    ?_⟩
  · rw [keepVacF_eq, e, finrank_su5]
  · rw [keepPlaneF_eq, e, finrank_plane5]
  · rw [keepLastDirectionF_eq, e, finrank_lastDirection5]

end Fock

end Comparison

end
