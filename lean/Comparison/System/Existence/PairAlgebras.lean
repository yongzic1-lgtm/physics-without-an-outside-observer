import Comparison.System.Existence.PairWhole

/-!
# The proof system, the existence layer: Proposition 46, the algebras

The rotations `½Γ_xΓ_y` of the ten lines are `so(10)`: `M ↦ ρ(M)` keeps
the commutator and is injective on the antisymmetric matrices. The real form `Z ↦ [[Re Z, −Im Z], [Im Z, Re Z]]` is
real-linear, multiplicative and injective and takes the anti-Hermitian `Z` to antisymmetric matrices, so
`Z ↦ ρ(realForm Z)` is an injective map of Lie algebras from `u(5)`; its image is the rotations keeping the comparison
(`keepLP`); `tr Z = 0` exactly on those keeping the singlet (`su(5)`); at the plane `{π 3, π 4}`, `Z` in
`s(u(3) ⊕ u(2))` (after the relabelling `π`) exactly on those keeping `N_F`, and in `su(3) ⊕ u(1)` exactly on those
keeping also the last-step direction's two-spinor state. The quarter of the comparison as an operator: `e^{−iπL/4} = −iP`
(`exp_quarter_comparison`), from its value on each of the sixteen two-spinor states, an eigenbasis of `L`.
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## The real form -/

theorem realForm_eq_uFive {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) : realForm Z = SysExt.uFive (realOf Z) := by
  rw [uFive_eq_realForm, zMat_realOf hZ]

theorem realForm_skew {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) : (realForm Z)ᵀ = -realForm Z := by
  rw [realForm_eq_uFive hZ]
  exact SysExt.uFive_mem_skew _

theorem realForm_add (Z W : Matrix (Fin 5) (Fin 5) ℂ) : realForm (Z + W) = realForm Z + realForm W := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [realForm] <;> ring

theorem realForm_real_smul (a : ℝ) (Z : Matrix (Fin 5) (Fin 5) ℂ) : realForm ((a : ℂ) • Z) = a • realForm Z := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [realForm]

theorem realForm_lie (Z W : Matrix (Fin 5) (Fin 5) ℂ) :
    realForm (Z * W - W * Z) = realForm Z * realForm W - realForm W * realForm Z := by
  rw [realForm_sub, realForm_mul, realForm_mul]

theorem realForm_submatrix (Z : Matrix (Fin 5) (Fin 5) ℂ) (π : Equiv.Perm (Fin 5)) :
    (realForm Z).submatrix (tenPerm π) (tenPerm π) = realForm (Z.submatrix π π) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> rfl

theorem antiHerm_submatrix {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) (π : Equiv.Perm (Fin 5)) :
    (Z.submatrix π π)ᴴ = -(Z.submatrix π π) := by
  rw [Matrix.conjTranspose_submatrix, hZ]
  rfl

/-! ## `u(5)` onto the rotations keeping the comparison -/

theorem turn_realForm_lie {Z W : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) :
    SysExt.turnOf tenLine (realForm Z) * SysExt.turnOf tenLine (realForm W) -
        SysExt.turnOf tenLine (realForm W) * SysExt.turnOf tenLine (realForm Z) =
      SysExt.turnOf tenLine (realForm (Z * W - W * Z)) := by
  rw [SysExt.turnOf_lie tenLine SysExt.tenLine_isTen _ _ (realForm_skew hZ), realForm_lie]

theorem turn_realForm_injective {Z W : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) (hW : Wᴴ = -W)
    (h : SysExt.turnOf tenLine (realForm Z) = SysExt.turnOf tenLine (realForm W)) : Z = W := by
  have e := skew_inj_turn (realForm_skew hZ) (realForm_skew hW) h
  have e0 : realForm (Z - W) = 0 := by rw [realForm_sub, e, sub_self]
  exact sub_eq_zero.mp (realForm_injective e0)

theorem turn_realForm_mem_keepLP {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) :
    SysExt.turnOf tenLine (realForm Z) ∈ keepLP :=
  (mem_keepLP _).mpr ⟨realOf Z, by rw [realForm_eq_uFive hZ]⟩

theorem keepLP_realForm (X : PairM) (hX : X ∈ keepLP) :
    ∃ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z ∧ SysExt.turnOf tenLine (realForm Z) = X := by
  obtain ⟨R, rfl⟩ := (mem_keepLP X).mp hX
  exact ⟨zMat R, zMat_antiHerm R, by rw [uFive_eq_realForm]⟩

/-! ## `su(5)`, and at every plane `s(u(3) ⊕ u(2))` and `su(3) ⊕ u(1)` -/

theorem turn_realForm_mem_keepVacP {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) :
    SysExt.turnOf tenLine (realForm Z) ∈ keepVacP ↔ Z.trace = 0 := by
  have htr : Z.trace = I * ((realOf Z).trace : ℂ) := by
    rw [← zMat_trace, zMat_realOf hZ]
  rw [keepVacP, Submodule.mem_inf, mem_annihP, realForm_eq_uFive hZ, vac_iff, htr, mul_eq_zero,
    Complex.ofReal_eq_zero]
  constructor
  · rintro ⟨-, h⟩
    exact Or.inr h
  · rintro (h | h)
    · exact absurd h Complex.I_ne_zero
    · exact ⟨(mem_keepLP _).mpr ⟨_, rfl⟩, h⟩

theorem turn_realForm_mem_keepPlaneP {W : Matrix (Fin 5) (Fin 5) ℂ} (hW : Wᴴ = -W) :
    SysExt.turnOf tenLine (realForm W) ∈ keepPlaneP ↔ GroupsContinuumLaw.IsPlaneTurn W := by
  rw [keepPlaneP_eq, Submodule.mem_map, realForm_eq_uFive hW]
  constructor
  · rintro ⟨R, hR, e⟩
    have hR' : R = realOf W := pairTurn_injective e
    rw [hR', zMat_plane_iff, zMat_realOf hW] at hR
    exact hR
  · intro h
    refine ⟨realOf W, (zMat_plane_iff _).mpr (by rw [zMat_realOf hW]; exact h), rfl⟩

theorem turn_realForm_mem_keepLastDirectionP {W : Matrix (Fin 5) (Fin 5) ℂ} (hW : Wᴴ = -W) :
    SysExt.turnOf tenLine (realForm W) ∈ keepLastDirectionP ↔ GroupsContinuumLaw.IsLastDirectionTurn W := by
  rw [keepLastDirectionP_eq, Submodule.mem_map, realForm_eq_uFive hW]
  constructor
  · rintro ⟨R, hR, e⟩
    have hR' : R = realOf W := pairTurn_injective e
    rw [hR', zMat_lastDirection_iff, zMat_realOf hW] at hR
    exact hR
  · intro h
    refine ⟨realOf W, (zMat_lastDirection_iff _).mpr (by rw [zMat_realOf hW]; exact h), rfl⟩

/-- **At the plane `{π 3, π 4}`:** the rotation of `Z` keeps the comparison, the singlet and `N_F` exactly when `Z` read
after the relabelling `π` is in `s(u(3) ⊕ u(2))`. -/
theorem turn_realForm_mem_plane (h k : Fin 5) (π : Equiv.Perm (Fin 5)) (e3 : π 3 = h) (e4 : π 4 = k)
    {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) :
    SysExt.turnOf tenLine (realForm Z) ∈ keepPlaneP' h k ↔ GroupsContinuumLaw.IsPlaneTurn (Z.submatrix π π) := by
  obtain ⟨hmem, -⟩ := carry_general keepPlaneP' keepPlaneF' keepPlaneP'_le keepPlaneF'_le transfer_plane
    keepPlane_map π 3 4 (realForm Z) (realForm_skew hZ)
  rw [e3, e4] at hmem
  rw [hmem, realForm_submatrix, keepPlane34P]
  exact turn_realForm_mem_keepPlaneP (antiHerm_submatrix hZ π)

/-- **At the plane `{π 3, π 4}` with the last-step direction `π 3`:** the rotation of `Z` keeps also the last-step direction's two-spinor state exactly when
`Z` read after the relabelling `π` is in `su(3) ⊕ u(1)`. -/
theorem turn_realForm_mem_lastDirection (h k : Fin 5) (π : Equiv.Perm (Fin 5)) (e3 : π 3 = h) (e4 : π 4 = k)
    {Z : Matrix (Fin 5) (Fin 5) ℂ} (hZ : Zᴴ = -Z) :
    SysExt.turnOf tenLine (realForm Z) ∈ keepLastDirectionP' h k ↔ GroupsContinuumLaw.IsLastDirectionTurn (Z.submatrix π π) := by
  obtain ⟨hmem, -⟩ := carry_general keepLastDirectionP' keepLastDirectionF' (fun a b _ hY => keepPlaneP'_le a b hY.1)
    (fun a b _ hY => keepPlaneF'_le a b hY.1) transfer_lastDirection keepLastDirection_map π 3 4 (realForm Z) (realForm_skew hZ)
  rw [e3, e4] at hmem
  rw [hmem, realForm_submatrix, keepLastDirection34P]
  exact turn_realForm_mem_keepLastDirectionP (antiHerm_submatrix hZ π)

/-! ## The quarter of the comparison as an operator -/

set_option backward.isDefEq.respectTransparency false in
/-- **On an eigenvector the exponential acts by the exponential of the eigenvalue.** -/
theorem exp_mulVec_of_eigen {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (v : m → ℂ) (μ : ℂ)
    (hv : A *ᵥ v = μ • v) : NormedSpace.exp A *ᵥ v = Complex.exp μ • v := by
  have hpow : ∀ n : ℕ, (A ^ n) *ᵥ v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  let f : Matrix m m ℂ →ₗ[ℂ] (m → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • A ^ n) *ᵥ v) (Complex.exp μ • v) := by
    have h3 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const v
    rw [← Complex.exp_eq_exp_ℂ] at h3
    refine h3.congr_fun fun n => ?_
    rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]
  open scoped Matrix.Norms.Operator in
  exact ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (LinearMap.toContinuousLinearMap f)).unique h2

theorem rel_card : Fintype.card (Fin 16) = Module.finrank ℂ (Two → ℂ) := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-- Two operators on the sixteen two-spinor states' space agree when they agree on the sixteen two-spinor states. -/
theorem matrix_eq_of_rel {M N : Matrix Two Two ℂ} (h : ∀ k : Fin 16, M *ᵥ rel k = N *ᵥ rel k) : M = N := by
  apply Matrix.toLin'.injective
  refine (basisOfLinearIndependentOfCardEqFinrank rel_linearIndependent rel_card).ext fun k => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h k

/-- **A quarter of the comparison is the swap:** `e^{−iπL/4} = −iP`. -/
theorem exp_quarter_comparison : NormedSpace.exp ((-(Real.pi / 4 : ℂ) * I) • L) = (-I) • swap := by
  apply matrix_eq_of_rel
  intro k
  have hv : ((-(Real.pi / 4 : ℂ) * I) • L) *ᵥ rel k = ((-(Real.pi / 4 : ℂ) * I) * (Lvalue k : ℂ)) • rel k := by
    rw [Matrix.smul_mulVec, L_rel', smul_smul]
  rw [exp_mulVec_of_eigen _ _ _ hv, Matrix.smul_mulVec, ← quarter_comparison k]
  congr 2
  ring

/-! ## Proposition 46 -/

/-- **Proposition 46 (the rotations of a pair, and what each keeps).** The ten lines of a pair on `H ⊗ H ⊗ ℂ²`,
`Γ_a = γ_a ⊗ 1 ⊗ σ_x`, `Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y`, anticommute, `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`; the two-spinor states are
`σ_z = +1`, on which the rotations `½Γ_xΓ_y` act as `γ_aγ_b ⊗ 1`, `1 ⊗ γ_aγ_b` and `iγ_a ⊗ γ_b` (times `½`); they are
`so(10)`: `M ↦ ρ(M) = ¼ Σ M_xy Γ_xΓ_y` keeps the commutator and is injective on the antisymmetric `M`, dimension
45; `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z` and `e^{−iπL/4} = −iP` (as an operator, and on each two-spinor state); the rotations
keeping the comparison are `u(5)`: `Z ↦ ρ([[Re Z, −Im Z], [Im Z, Re Z]])` is an injective real-linear map of Lie
algebras from the anti-Hermitian `5 × 5` matrices onto them, 25 (keeping `L ⊗ 1` likewise), with centre
`ℝ·i(L − 1) ⊗ σ_z`, the rotation `ρ(J) = ½ i(L − 1) ⊗ σ_z` of the complex structure; keeping also the singlet `Ω ⊗ e₊`:
`tr Z = 0`, `su(5)`, 24; keeping also the plane count `N_F = Σ_{t ∈ F}(1 − (γ_t ⊗ γ_t) ⊗ σ_z)/2`: `Z` in
`s(u(3) ⊕ u(2))`, 12, with centre `ℝ·ρ(iY)`; keeping also the last-step direction's two-spinor state `ℓ_h ⊗ e₊`: `Z` in `su(3) ⊕ u(1)`, 9,
with centre `ℝ·ρ(iQ)` — at every plane `F = {h, k}` with the last-step direction `h` (`Z` read after a relabelling `π` with
`π 3 = h`, `π 4 = k`; `Y = ½` on `F`, `−⅓` on `C`; `Q = 0` on `h`, `1` on `k`, `−⅓` on `C`);
`(A, B, z) ↦ (z²A, z̄³B)` maps `SU(3) × SU(2) × U(1)` onto `S(U(3) × U(2))`, with kernel the six images of the sixth
roots of unity, cyclic, and `(SU(3) × SU(2) × U(1))/ℤ₆ ≃ S(U(3) × U(2))`; and on the sixteen, at every plane,
`Tr Y = Tr Y³ = 0` and the colour and the doublet sums of `Y` vanish (`Tr YT_c² = Tr YT₃² = 0`).

Recognition: the gauge group of the standard model, `S(U(2) × U(3)) = (SU(3) × SU(2) × U(1))/ℤ₆`, twelve
generators, held by `SU(5)`; `Y` the hypercharge, `Q` the electric charge. Uses Props. 4, 10, 11, 45. -/
theorem prop_46_full :
    ((∀ x y : SysExt.Ten, tenLine x * tenLine y + tenLine y * tenLine x = if x = y then (2 : ℂ) • 1 else 0) ∧
    Module.finrank ℝ (SysExt.turnsTen tenLine) = 45 ∧
    (-I) • ∑ t, tenLine (Sum.inl t) * tenLine (Sum.inr t) = (L - 1) ⊗ₖ σ₃ ∧
    (∀ k : Fin 16, Complex.exp (-(Real.pi / 4 : ℂ) * (Lvalue k : ℂ) * I) • rel k = (-I) • (swap *ᵥ rel k)) ∧
    Module.finrank ℝ keepLP = 25 ∧
    Module.finrank ℝ (SysExt.turnsTen tenLine ⊓ SysExt.commWith (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
      Submodule ℝ _) = 25 ∧
    SysExt.turnOf tenLine SysExt.cxJ = (1 / 2 : ℝ) • (I • ((L - 1) ⊗ₖ σ₃)) ∧
    vacP = kronVec Ω (Pi.single 0 1) ∧ Module.finrank ℝ keepVacP = 24 ∧
    planeNP = (1 / 2 : ℂ) • (1 - (γ 3 ⊗ₖ γ 3) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ 4 ⊗ₖ γ 4) ⊗ₖ σ₃) ∧
    Module.finrank ℝ keepPlaneP = 12 ∧
    lastDirectionP = kronVec (ell 3) (Pi.single 0 1) ∧ Module.finrank ℝ keepLastDirectionP = 9 ∧
    (GroupsContinuumLaw.IsPlaneTurn GroupsContinuumLaw.Yc ∧ (∀ W, GroupsContinuumLaw.IsPlaneTurn W → GroupsContinuumLaw.Yc * W = W * GroupsContinuumLaw.Yc) ∧
      ∀ Z, GroupsContinuumLaw.IsPlaneTurn Z → (∀ W, GroupsContinuumLaw.IsPlaneTurn W → Z * W = W * Z) →
        ∃ a : ℝ, Z = (a : ℂ) • GroupsContinuumLaw.Yc) ∧
    (GroupsContinuumLaw.IsLastDirectionTurn GroupsContinuumLaw.Qc ∧ (∀ W, GroupsContinuumLaw.IsLastDirectionTurn W → GroupsContinuumLaw.Qc * W = W * GroupsContinuumLaw.Qc) ∧
      ∀ Z, GroupsContinuumLaw.IsLastDirectionTurn Z → (∀ W, GroupsContinuumLaw.IsLastDirectionTurn W → Z * W = W * Z) →
        ∃ a : ℝ, Z = (a : ℂ) • GroupsContinuumLaw.Qc) ∧
    Function.Surjective GroupsContinuumLaw.symHom ∧
    (∀ x, GroupsContinuumLaw.symHom x = 1 ↔ ∃ ζ : rootsOfUnity 6 ℂ, x = GroupsContinuumLaw.kerElt ζ) ∧
    Nat.card (rootsOfUnity 6 ℂ) = 6 ∧ IsCyclic (rootsOfUnity 6 ℂ) ∧
    (∑ S ∈ GroupsContinuumLaw.relSets, GroupsContinuumLaw.chargeZ GroupsContinuumLaw.y6 S = 0 ∧
      ∑ S ∈ GroupsContinuumLaw.relSets, GroupsContinuumLaw.chargeZ GroupsContinuumLaw.y6 S ^ 3 = 0)) ∧
    (∀ h k : Fin 5, h ≠ k →
      crP h * anP h + crP k * anP k =
        (1 / 2 : ℂ) • (1 - (γ h ⊗ₖ γ h) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ k ⊗ₖ γ k) ⊗ₖ σ₃) ∧
      lastDirectionAtP h = kronVec (ell h) (Pi.single 0 1) ∧
      Module.finrank ℝ (keepPlaneP' h k) = 12 ∧ Module.finrank ℝ (keepLastDirectionP' h k) = 9) ∧
    (∀ (a b : Fin 5) (r : Two → ℂ),
      (tenLine (Sum.inl a) * tenLine (Sum.inl b)) *ᵥ kronVec r (Pi.single 0 1) =
        kronVec (((γ a * γ b) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ r) (Pi.single 0 1) ∧
      (tenLine (Sum.inr a) * tenLine (Sum.inr b)) *ᵥ kronVec r (Pi.single 0 1) =
        kronVec (((1 : Matrix Four Four ℂ) ⊗ₖ (γ a * γ b)) *ᵥ r) (Pi.single 0 1) ∧
      (tenLine (Sum.inl a) * tenLine (Sum.inr b)) *ᵥ kronVec r (Pi.single 0 1) =
        kronVec ((I • (γ a ⊗ₖ γ b)) *ᵥ r) (Pi.single 0 1)) ∧
    (∀ X : PairM, X ∈ SysExt.turnsTen tenLine ↔
      ∃ M : Matrix SysExt.Ten SysExt.Ten ℝ, Mᵀ = -M ∧ SysExt.turnOf tenLine M = X) ∧
    (∀ M N : Matrix SysExt.Ten SysExt.Ten ℝ, Mᵀ = -M →
      SysExt.turnOf tenLine M * SysExt.turnOf tenLine N - SysExt.turnOf tenLine N * SysExt.turnOf tenLine M =
        SysExt.turnOf tenLine (M * N - N * M)) ∧
    (∀ M : Matrix SysExt.Ten SysExt.Ten ℝ, Mᵀ = -M → SysExt.turnOf tenLine M = 0 → M = 0) ∧
    NormedSpace.exp ((-(Real.pi / 4 : ℂ) * I) • L) = (-I) • swap ∧
    (∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z → (realForm Z)ᵀ = -realForm Z) ∧
    (∀ (a : ℝ) (Z W : Matrix (Fin 5) (Fin 5) ℂ), realForm ((a : ℂ) • Z + W) = a • realForm Z + realForm W) ∧
    (∀ Z W : Matrix (Fin 5) (Fin 5) ℂ,
      realForm (Z * W - W * Z) = realForm Z * realForm W - realForm W * realForm Z) ∧
    (∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z → SysExt.turnOf tenLine (realForm Z) ∈ keepLP) ∧
    (∀ X ∈ keepLP, ∃ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z ∧ SysExt.turnOf tenLine (realForm Z) = X) ∧
    (∀ Z W : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z → Wᴴ = -W →
      SysExt.turnOf tenLine (realForm Z) = SysExt.turnOf tenLine (realForm W) → Z = W) ∧
    (∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z → (SysExt.turnOf tenLine (realForm Z) ∈ keepVacP ↔ Z.trace = 0)) ∧
    (∀ h k : Fin 5, h ≠ k → ∃ π : Equiv.Perm (Fin 5), π 3 = h ∧ π 4 = k) ∧
    (∀ (h k : Fin 5) (π : Equiv.Perm (Fin 5)), π 3 = h → π 4 = k → ∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Zᴴ = -Z →
      (SysExt.turnOf tenLine (realForm Z) ∈ keepPlaneP' h k ↔ GroupsContinuumLaw.IsPlaneTurn (Z.submatrix π π)) ∧
      (SysExt.turnOf tenLine (realForm Z) ∈ keepLastDirectionP' h k ↔ GroupsContinuumLaw.IsLastDirectionTurn (Z.submatrix π π))) ∧
    (∀ X ∈ keepLP, (∀ Y ∈ keepLP, X * Y = Y * X) ↔ ∃ a : ℝ, X = a • (I • ((L - 1) ⊗ₖ σ₃))) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ X ∈ keepPlaneP' h k, (∀ Y ∈ keepPlaneP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (yAt h k)))) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ X ∈ keepLastDirectionP' h k, (∀ Y ∈ keepLastDirectionP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (qAt h k)))) ∧
    Nonempty (((GroupsContinuumLaw.SU3 × GroupsContinuumLaw.SU2 × GroupsContinuumLaw.U1) ⧸ GroupsContinuumLaw.symHom.ker) ≃* GroupsContinuumLaw.SU32) ∧
    (∀ h k : Fin 5, h ≠ k → ∑ r, hyper h k r = 0 ∧ ∑ r, hyper h k r ^ 3 = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper h k r = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper h k r = 0) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := prop_46
  refine ⟨q1, q2, q3, fun X => ?_, fun M N hM => SysExt.turnOf_lie tenLine SysExt.tenLine_isTen M N hM,
    fun M hM h0 => SysExt.turnOf_eq_zero tenLine SysExt.tenLine_isTen M hM h0, exp_quarter_comparison,
    fun Z hZ => realForm_skew hZ, fun a Z W => by rw [realForm_add, realForm_real_smul], realForm_lie,
    fun Z hZ => turn_realForm_mem_keepLP hZ, keepLP_realForm, fun Z W hZ hW h => turn_realForm_injective hZ hW h,
    fun Z hZ => turn_realForm_mem_keepVacP hZ, exists_perm34,
    fun h k π e3 e4 Z hZ => ⟨turn_realForm_mem_plane h k π e3 e4 hZ, turn_realForm_mem_lastDirection h k π e3 e4 hZ⟩,
    q4, q5, q6, q7, q8⟩
  rw [SysExt.turnsTen, Submodule.mem_map]
  exact ⟨fun ⟨M, hM, e⟩ => ⟨M, hM, e⟩, fun ⟨M, hM, e⟩ => ⟨M, hM, e⟩⟩

end Comparison.System.Existence
