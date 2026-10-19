import Comparison.System.Existence.PairPlanes
import Comparison.System.Existence.PairCentres
import Comparison.System.Existence.Matter

/-!
# The proof system, the existence layer: Proposition 46 whole

The products of the ten lines act on the two-spinor states (`σ_z = +1`) as `γ_aγ_b ⊗ 1`,
`1 ⊗ γ_aγ_b` and `iγ_a ⊗ γ_b` (`tenLine_on_relations`). The centre of `u(5)` is `ℝ·i` (`u5_centre`), so the centre of
the pair's rotations that keep the comparison is `ℝ·i(L − 1) ⊗ σ_z` (`pair_L_centre`). At every plane `{h, k}` the centre
of the pair's `s(u(3) ⊕ u(2))` is `ℝ·ρ(iY)`, `Y = ½` on the plane and `−⅓` outside, and that of its `su(3) ⊕ u(1)` is
`ℝ·ρ(iQ)`, `Q = 0` on the last-step direction, `1` on `k`, `−⅓` outside (`pair_plane_centre_every`, `pair_lastDirection_centre_every`):
two rotations commute exactly when their skew matrices do (`turn_comm_iff`), so centrality is read on the skew matrices
(`central_transfer`); the relabelling `Λ(P_π)` is an automorphism (`conjE_mul`) carrying the rotations that keep `{a, b}`
to those that keep `{πa, πb}`, hence their centres (`carry_general`); and `P_π` carries `diag(d)` to `diag(d ∘ π⁻¹)`
(`uFive_diagonal_perm`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## The ten lines on the two-spinor states -/

/-- **The products of the ten lines:** `Γ_aΓ_b = γ_aγ_b ⊗ 1 ⊗ 1`, `Γ_{5+a}Γ_{5+b} = 1 ⊗ γ_aγ_b ⊗ 1`,
`Γ_aΓ_{5+b} = γ_a ⊗ γ_b ⊗ iσ_z`. -/
theorem tenLine_products (a b : Fin 5) :
    tenLine (Sum.inl a) * tenLine (Sum.inl b) =
      ((γ a * γ b) ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    tenLine (Sum.inr a) * tenLine (Sum.inr b) =
      ((1 : Matrix Four Four ℂ) ⊗ₖ (γ a * γ b)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    tenLine (Sum.inl a) * tenLine (Sum.inr b) = (γ a ⊗ₖ γ b) ⊗ₖ (I • σ₃) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [tenLine, kron3_mul, Matrix.mul_one, σ₁_sq]
  · simp only [tenLine, kron3_mul, Matrix.one_mul, σ₂_sq]
  · simp only [tenLine, kron3_mul, Matrix.mul_one, Matrix.one_mul, σ₁σ₂_eq]

/-- **The rotations `½Γ_xΓ_y` on the two-spinor states** (`σ_z = +1`): `Γ_aΓ_b`, `Γ_{5+a}Γ_{5+b}` and `Γ_aΓ_{5+b}` act on
`r ⊗ e₊` as `γ_aγ_b ⊗ 1`, `1 ⊗ γ_aγ_b` and `iγ_a ⊗ γ_b` act on `r`. -/
theorem tenLine_on_relations (a b : Fin 5) (r : Two → ℂ) :
    (tenLine (Sum.inl a) * tenLine (Sum.inl b)) *ᵥ kronVec r (Pi.single 0 1) =
      kronVec (((γ a * γ b) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ r) (Pi.single 0 1) ∧
    (tenLine (Sum.inr a) * tenLine (Sum.inr b)) *ᵥ kronVec r (Pi.single 0 1) =
      kronVec (((1 : Matrix Four Four ℂ) ⊗ₖ (γ a * γ b)) *ᵥ r) (Pi.single 0 1) ∧
    (tenLine (Sum.inl a) * tenLine (Sum.inr b)) *ᵥ kronVec r (Pi.single 0 1) =
      kronVec ((I • (γ a ⊗ₖ γ b)) *ᵥ r) (Pi.single 0 1) := by
  obtain ⟨e1, e2, e3⟩ := tenLine_products a b
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, kron_mulVec_kronVec, Matrix.one_mulVec]
  · rw [e2, kron_mulVec_kronVec, Matrix.one_mulVec]
  · rw [e3, Matrix.kronecker_smul, ← Matrix.smul_kronecker, kronVec_e₀_σ₃]

/-! ## The centre of `u(5)` and of the pair's rotations keeping the comparison -/

theorem tA_antiHerm (s t : Fin 5) (hst : s ≠ t) : (GroupsContinuumLaw.tA s t)ᴴ = -GroupsContinuumLaw.tA s t := by
  ext i j
  simp only [GroupsContinuumLaw.tA, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.neg_apply]
  split_ifs <;> simp_all

theorem tB_antiHerm (s t : Fin 5) (hst : s ≠ t) : (GroupsContinuumLaw.tB s t)ᴴ = -GroupsContinuumLaw.tB s t := by
  ext i j
  simp only [GroupsContinuumLaw.tB, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.neg_apply, smul_eq_mul]
  split_ifs <;> simp_all

/-- **The centre of `u(5)` is `ℝ·i`:** an anti-Hermitian `5 × 5` matrix that commutes with every anti-Hermitian one
is `a·i` for a real `a`. -/
theorem u5_centre (Z : Matrix (Fin 5) (Fin 5) ℂ) (hZ : Zᴴ = -Z)
    (hc : ∀ W : Matrix (Fin 5) (Fin 5) ℂ, Wᴴ = -W → Z * W = W * Z) :
    ∃ a : ℝ, Z = (a : ℂ) • (I • (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
  have T : ∀ s t : Fin 5, s ≠ t → Z s s = Z t t ∧ Z s t = 0 := fun s t hst =>
    GroupsContinuumLaw.comm_tests Z s t hst (hc _ (tA_antiHerm s t hst)) (hc _ (tB_antiHerm s t hst))
  have h00 := GroupsContinuumLaw.antiherm_diag hZ 0
  set a := (Z 0 0).im with ha
  refine ⟨a, ?_⟩
  ext i j
  by_cases hij : i = j
  · rw [← hij]
    have hi : Z i i = Z 0 0 := by
      by_cases h0 : i = 0
      · rw [h0]
      · exact (T i 0 h0).1
    rw [hi, h00]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · rw [(T i j hij).2]
    simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]

theorem skA_diagonal (d : Fin 5 → ℝ) : SysExt.skA (Matrix.diagonal d) = 0 := by
  ext s t
  simp only [SysExt.skA, Matrix.of_apply, Matrix.zero_apply]
  by_cases h1 : s < t
  · rw [if_pos h1, Matrix.diagonal_apply_ne _ (ne_of_lt h1)]
  · by_cases h2 : t < s
    · rw [if_neg h1, if_pos h2, Matrix.diagonal_apply_ne _ (ne_of_lt h2), neg_zero]
    · rw [if_neg h1, if_neg h2]

theorem syB_diagonal (d : Fin 5 → ℝ) : SysExt.syB (Matrix.diagonal d) = Matrix.diagonal d := by
  ext s t
  by_cases hst : s = t
  · rw [← hst]
    simp [SysExt.syB]
  · simp only [SysExt.syB, Matrix.of_apply, Matrix.diagonal_apply_ne _ hst, Matrix.diagonal_apply_ne _ (Ne.symm hst),
      ite_self]

/-- The rotation of a diagonal `5 × 5` matrix: `uFive (diag d) = [[0, −diag d], [diag d, 0]]`. -/
theorem uFive_diagonal (d : Fin 5 → ℝ) :
    SysExt.uFive (Matrix.diagonal d) = Matrix.fromBlocks 0 (-Matrix.diagonal d) (Matrix.diagonal d) 0 := by
  rw [SysExt.uFive_apply, skA_diagonal, syB_diagonal]

theorem uFive_one : SysExt.uFive 1 = -SysExt.cxJ := by
  rw [← Matrix.diagonal_one, uFive_diagonal, Matrix.diagonal_one, SysExt.cxJ, Matrix.fromBlocks_neg, neg_zero,
    neg_neg]

/-- **Two rotations commute exactly when their skew matrices do.** -/
theorem turn_comm_iff {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A] (Γ : SysExt.Ten → A)
    (hΓ : SysExt.IsTen Γ) (M N : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M) (hN : Nᵀ = -N) :
    SysExt.turnOf Γ M * SysExt.turnOf Γ N = SysExt.turnOf Γ N * SysExt.turnOf Γ M ↔ M * N = N * M := by
  rw [← sub_eq_zero, SysExt.turnOf_lie Γ hΓ M N hM]
  constructor
  · intro h
    exact sub_eq_zero.mp (SysExt.turnOf_eq_zero Γ hΓ _ (SysExt.comm_skew M N hM hN) h)
  · intro h
    rw [sub_eq_zero.mpr h, map_zero]

/-- **The centre of the pair's `u(5)` is `ℝ·i(L − 1) ⊗ σ_z`**, the rotation `ρ(J)` of the complex structure: a rotation
keeping the comparison commutes with all of them exactly when it is a real multiple of `i(L − 1) ⊗ σ_z`. -/
theorem pair_L_centre (X : PairM) (hX : X ∈ keepLP) :
    (∀ Y ∈ keepLP, X * Y = Y * X) ↔ ∃ a : ℝ, X = a • (I • ((L - 1) ⊗ₖ σ₃)) := by
  obtain ⟨R, rfl⟩ := (mem_keepLP X).mp hX
  have hJ : SysExt.turnOf tenLine (SysExt.uFive 1) = -((1 / 2 : ℝ) • (I • ((L - 1) ⊗ₖ σ₃))) := by
    rw [uFive_one, map_neg, SysExt.turnOf_cxJ tenLine SysExt.tenLine_isTen, SysExt.pairSum_tenLine]
  constructor
  · intro hc
    have hcomm : ∀ W : Matrix (Fin 5) (Fin 5) ℂ, Wᴴ = -W → zMat R * W = W * zMat R := by
      intro W hW
      have h1 := hc _ ((mem_keepLP _).mpr ⟨realOf W, rfl⟩)
      rw [← zMat_realOf hW]
      exact (comm_iff_zMat R (realOf W)).mp h1
    obtain ⟨a, ha⟩ := u5_centre (zMat R) (zMat_antiHerm R) hcomm
    have hRa : R = a • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
      apply zMat_injective
      rw [ha, show a • (1 : Matrix (Fin 5) (Fin 5) ℝ) = Matrix.diagonal (fun _ => a) from
        Matrix.smul_one_eq_diagonal a, zMat_diag]
      ext i j
      by_cases hij : i = j
      · rw [← hij]
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul, mul_one]
        ring
      · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, smul_zero]
    refine ⟨-(a / 2), ?_⟩
    rw [hRa, map_smul, map_smul, hJ, smul_neg, smul_smul, ← neg_smul]
    congr 1
    ring
  · rintro ⟨a, ha⟩ Y hY
    obtain ⟨R', rfl⟩ := (mem_keepLP Y).mp hY
    have hX : SysExt.turnOf tenLine (SysExt.uFive R) = (-2 * a) • SysExt.turnOf tenLine (SysExt.uFive 1) := by
      rw [ha, hJ, smul_neg, smul_smul, ← neg_smul]
      congr 1
      ring
    have hc := (turn_comm_iff tenLine SysExt.tenLine_isTen (SysExt.uFive 1) (SysExt.uFive R')
      (SysExt.uFive_mem_skew 1) (SysExt.uFive_mem_skew R')).mpr
      (by rw [uFive_one, Matrix.neg_mul, Matrix.mul_neg, SysExt.uFive_comm])
    rw [hX, smul_mul_assoc, hc, mul_smul_comm]

/-! ## The centres at every plane -/

/-- **Centrality is read on the skew matrices:** two subspaces of rotations with the same skew matrices have the same
centre. -/
theorem central_transfer (KP : Submodule ℝ PairM) (KF : Submodule ℝ SysExt.FockE)
    (hP : KP ≤ SysExt.turnsTen tenLine) (hF : KF ≤ SysExt.turnsTen SysExt.fockLine)
    (h : ∀ M : Matrix SysExt.Ten SysExt.Ten ℝ, Mᵀ = -M →
      (SysExt.turnOf tenLine M ∈ KP ↔ SysExt.turnOf SysExt.fockLine M ∈ KF))
    (M : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M) :
    (∀ Y ∈ KP, SysExt.turnOf tenLine M * Y = Y * SysExt.turnOf tenLine M) ↔
      ∀ Y ∈ KF, SysExt.turnOf SysExt.fockLine M * Y = Y * SysExt.turnOf SysExt.fockLine M := by
  constructor
  · intro hc Y hY
    obtain ⟨N, hN, rfl⟩ := hF hY
    have hN' : Nᵀ = -N := hN
    have h1 := hc _ ((h N hN').mpr hY)
    rw [turn_comm_iff tenLine SysExt.tenLine_isTen M N hM hN'] at h1
    exact (turn_comm_iff SysExt.fockLine SysExt.fockLine_isTen M N hM hN').mpr h1
  · intro hc Y hY
    obtain ⟨N, hN, rfl⟩ := hP hY
    have hN' : Nᵀ = -N := hN
    have h1 := hc _ ((h N hN').mp hY)
    rw [turn_comm_iff SysExt.fockLine SysExt.fockLine_isTen M N hM hN'] at h1
    exact (turn_comm_iff tenLine SysExt.tenLine_isTen M N hM hN').mpr h1

/-- The relabelling is an automorphism: `Λ(P_π)(XY)Λ(P_π)⁻¹ = (Λ(P_π)XΛ(P_π)⁻¹)(Λ(P_π)YΛ(P_π)⁻¹)`. -/
theorem conjE_mul (π : Equiv.Perm (Fin 5)) (X Y : SysExt.FockE) :
    conjE π (X * Y) = conjE π X * conjE π Y := by
  obtain ⟨-, h2⟩ := relabel_inv π
  simp only [conjE_apply]
  calc relabel π * (X * Y) * relabel π⁻¹ = relabel π * X * 1 * Y * relabel π⁻¹ := by noncomm_ring
    _ = relabel π * X * (relabel π⁻¹ * relabel π) * Y * relabel π⁻¹ := by rw [h2]
    _ = relabel π * X * relabel π⁻¹ * (relabel π * Y * relabel π⁻¹) := by noncomm_ring

/-- **A relabelling carries what is kept at `{a, b}`, and its centre, to `{πa, πb}`:** for families of kept rotations
of the pair and of `Λℂ⁵` with the same skew matrices, the second carried by the relabellings, a rotation `ρ(M)` is kept at
`{πa, πb}` exactly when `ρ(P_π⁻¹MP_π)` is kept at `{a, b}`, and is central there exactly when `ρ(P_π⁻¹MP_π)` is
central at `{a, b}`. -/
theorem carry_general (KP : Fin 5 → Fin 5 → Submodule ℝ PairM) (KF : Fin 5 → Fin 5 → Submodule ℝ SysExt.FockE)
    (hP : ∀ a b, KP a b ≤ SysExt.turnsTen tenLine) (hF : ∀ a b, KF a b ≤ SysExt.turnsTen SysExt.fockLine)
    (htr : ∀ (a b : Fin 5) (M : Matrix SysExt.Ten SysExt.Ten ℝ), Mᵀ = -M →
      (SysExt.turnOf tenLine M ∈ KP a b ↔ SysExt.turnOf SysExt.fockLine M ∈ KF a b))
    (hmap : ∀ (π : Equiv.Perm (Fin 5)) (a b : Fin 5), KF (π a) (π b) = (KF a b).map (conjE π).toLinearMap)
    (π : Equiv.Perm (Fin 5)) (a b : Fin 5) (M : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M) :
    (SysExt.turnOf tenLine M ∈ KP (π a) (π b) ↔
        SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π)) ∈ KP a b) ∧
    ((∀ Y ∈ KP (π a) (π b), SysExt.turnOf tenLine M * Y = Y * SysExt.turnOf tenLine M) ↔
      ∀ Y ∈ KP a b, SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π)) * Y =
        Y * SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π))) := by
  have hM₀s : (M.submatrix (tenPerm π) (tenPerm π))ᵀ = -(M.submatrix (tenPerm π) (tenPerm π)) := by
    rw [Matrix.transpose_submatrix, hM]
    rfl
  have hMM : (M.submatrix (tenPerm π) (tenPerm π)).submatrix (tenPerm π).symm (tenPerm π).symm = M := by
    rw [Matrix.submatrix_submatrix]
    simp
  have hconj : SysExt.turnOf SysExt.fockLine M =
      conjE π (SysExt.turnOf SysExt.fockLine (M.submatrix (tenPerm π) (tenPerm π))) := by
    obtain ⟨h1, -⟩ := relabel_inv π
    rw [conjE_apply, relabel_turn, mul_assoc, h1, mul_one, hMM]
  have hmemF : SysExt.turnOf SysExt.fockLine M ∈ KF (π a) (π b) ↔
      SysExt.turnOf SysExt.fockLine (M.submatrix (tenPerm π) (tenPerm π)) ∈ KF a b := by
    rw [hconj, hmap π a b]
    constructor
    · rintro ⟨Y, hY, hYe⟩
      have : Y = SysExt.turnOf SysExt.fockLine (M.submatrix (tenPerm π) (tenPerm π)) := (conjE π).injective hYe
      rw [← this]
      exact hY
    · intro hY
      exact ⟨_, hY, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [htr _ _ M hM, htr _ _ _ hM₀s, hmemF]
  · rw [central_transfer (KP (π a) (π b)) (KF (π a) (π b)) (hP _ _) (hF _ _) (htr _ _) M hM,
      central_transfer (KP a b) (KF a b) (hP _ _) (hF _ _) (htr _ _) _ hM₀s, hconj, hmap π a b]
    constructor
    · intro hc Y hY
      have h1 := hc (conjE π Y) ⟨Y, hY, rfl⟩
      rw [← conjE_mul, ← conjE_mul] at h1
      exact (conjE π).injective h1
    · rintro hc _ ⟨Y, hY, rfl⟩
      change conjE π _ * conjE π Y = conjE π Y * conjE π _
      rw [← conjE_mul, ← conjE_mul, hc Y hY]

/-- `P_π` carries the rotation of `diag(d)` to the rotation of `diag(d ∘ π⁻¹)`. -/
theorem uFive_diagonal_perm (π : Equiv.Perm (Fin 5)) (d : Fin 5 → ℝ) :
    (SysExt.uFive (Matrix.diagonal d)).submatrix (tenPerm π).symm (tenPerm π).symm =
      SysExt.uFive (Matrix.diagonal (d ∘ π.symm)) := by
  rw [uFive_diagonal, uFive_diagonal]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [tenPerm, Matrix.submatrix_apply, Matrix.diagonal_apply]

/-- The hypercharge at the plane `{h, k}`: `½` on the two lines of the plane, `−⅓` on the three outside. -/
noncomputable def yAt (h k : Fin 5) : Fin 5 → ℝ := fun s => if s = h ∨ s = k then 1 / 2 else -1 / 3

/-- The charge at the last-step direction `h` of the plane `{h, k}`: `0` on `h`, `1` on `k`, `−⅓` on the three outside. -/
noncomputable def qAt (h k : Fin 5) : Fin 5 → ℝ := fun s => if s = h then 0 else if s = k then 1 else -1 / 3

theorem yAt_perm (π : Equiv.Perm (Fin 5)) {h k : Fin 5} (e3 : π 3 = h) (e4 : π 4 = k) :
    yAt h k = yAt 3 4 ∘ π.symm := by
  funext s
  simp only [yAt, Function.comp_apply, Equiv.symm_apply_eq, e3, e4]

theorem qAt_perm (π : Equiv.Perm (Fin 5)) {h k : Fin 5} (e3 : π 3 = h) (e4 : π 4 = k) :
    qAt h k = qAt 3 4 ∘ π.symm := by
  funext s
  simp only [qAt, Function.comp_apply, Equiv.symm_apply_eq, e3, e4]

theorem RY_eq : RY = Matrix.diagonal (yAt 3 4) := by
  rw [RY]
  congr 1
  funext s
  fin_cases s <;> simp [yAt]

theorem RQ_eq : RQ = Matrix.diagonal (qAt 3 4) := by
  rw [RQ]
  congr 1
  funext s
  fin_cases s <;> simp [qAt]

theorem keepPlane34P : keepPlaneP' 3 4 = keepPlaneP := rfl

theorem keepLastDirection34P : keepLastDirectionP' 3 4 = keepLastDirectionP := rfl

theorem exists_perm34 (h k : Fin 5) (hk : h ≠ k) : ∃ π : Equiv.Perm (Fin 5), π 3 = h ∧ π 4 = k :=
  ⟨_, perm_to_plane h k hk⟩

/-- A rotation of the pair is known by its skew matrix. -/
theorem skew_inj_turn {N N' : Matrix SysExt.Ten SysExt.Ten ℝ} (hN : Nᵀ = -N) (hN' : N'ᵀ = -N')
    (e : SysExt.turnOf tenLine N = SysExt.turnOf tenLine N') : N = N' := by
  have hs : (N - N')ᵀ = -(N - N') := by
    rw [Matrix.transpose_sub, hN, hN']
    abel
  exact sub_eq_zero.mp (SysExt.turnOf_eq_zero tenLine SysExt.tenLine_isTen _ hs (by rw [map_sub, e, sub_self]))

theorem submatrix_smul' {m n l o : Type*} (a : ℝ) (A : Matrix m n ℝ) (r : l → m) (c : o → n) :
    (a • A).submatrix r c = a • A.submatrix r c := rfl

/-- The last step: the centre at `{3, 4}` read at `{πa, πb}`. -/
theorem centre_finish (π : Equiv.Perm (Fin 5)) (M : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M)
    (R₀ : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ)
    (hd : SysExt.uFive (Matrix.diagonal d) = (SysExt.uFive R₀).submatrix (tenPerm π).symm (tenPerm π).symm) :
    (∃ a : ℝ, SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π)) =
        a • SysExt.turnOf tenLine (SysExt.uFive R₀)) ↔
      ∃ a : ℝ, SysExt.turnOf tenLine M = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal d)) := by
  have hU : (SysExt.uFive R₀)ᵀ = -SysExt.uFive R₀ := SysExt.uFive_mem_skew R₀
  have hs0 : (M.submatrix (tenPerm π) (tenPerm π))ᵀ = -(M.submatrix (tenPerm π) (tenPerm π)) := by
    rw [Matrix.transpose_submatrix, hM]
    rfl
  refine exists_congr fun a => ?_
  have hs1 : (a • SysExt.uFive R₀)ᵀ = -(a • SysExt.uFive R₀) := by
    rw [Matrix.transpose_smul, hU, smul_neg]
  have hs2 : (a • (SysExt.uFive R₀).submatrix (tenPerm π).symm (tenPerm π).symm)ᵀ =
      -(a • (SysExt.uFive R₀).submatrix (tenPerm π).symm (tenPerm π).symm) := by
    rw [Matrix.transpose_smul, Matrix.transpose_submatrix, hU, ← smul_neg]
    rfl
  have e1 : (a • SysExt.turnOf tenLine (SysExt.uFive R₀) : PairM) = SysExt.turnOf tenLine (a • SysExt.uFive R₀) :=
    (map_smul _ _ _).symm
  have e2 : (a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal d)) : PairM) =
      SysExt.turnOf tenLine (a • (SysExt.uFive R₀).submatrix (tenPerm π).symm (tenPerm π).symm) := by
    rw [hd]
    exact (map_smul _ _ _).symm
  rw [e1, e2]
  constructor
  · intro e
    have e' := skew_inj_turn hs0 hs1 e
    congr 1
    rw [← submatrix_smul', ← e', Matrix.submatrix_submatrix]
    simp
  · intro e
    have e' := skew_inj_turn hM hs2 e
    congr 1
    rw [e', submatrix_smul', Matrix.submatrix_submatrix]
    simp

/-- **At every plane `{h, k}` the centre of the pair's `s(u(3) ⊕ u(2))` is `ℝ·ρ(iY)`,** `Y = ½` on the plane and
`−⅓` on the three lines outside it. -/
theorem pair_plane_centre_every (h k : Fin 5) (hk : h ≠ k) (X : PairM) (hX : X ∈ keepPlaneP' h k) :
    (∀ Y ∈ keepPlaneP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (yAt h k))) := by
  obtain ⟨π, e3, e4⟩ := exists_perm34 h k hk
  obtain ⟨M, hM, rfl⟩ := keepPlaneP'_le h k hX
  have hM' : Mᵀ = -M := hM
  obtain ⟨hmem, hcent⟩ := carry_general keepPlaneP' keepPlaneF' keepPlaneP'_le keepPlaneF'_le transfer_plane
    keepPlane_map π 3 4 M hM'
  rw [e3, e4] at hmem hcent
  have hm0 : SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π)) ∈ keepPlaneP := by
    rw [← keepPlane34P]
    exact hmem.mp hX
  rw [hcent, keepPlane34P, pair_plane_centre _ hm0]
  exact centre_finish π M hM' RY (yAt h k) (by rw [RY_eq, uFive_diagonal_perm, ← yAt_perm π e3 e4])

/-- **At every plane `{h, k}` with the last-step direction `h`, the centre of the pair's `su(3) ⊕ u(1)` is `ℝ·ρ(iQ)`,** `Q = 0` on
the last-step direction, `1` on `k` and `−⅓` on the three lines outside. -/
theorem pair_lastDirection_centre_every (h k : Fin 5) (hk : h ≠ k) (X : PairM) (hX : X ∈ keepLastDirectionP' h k) :
    (∀ Y ∈ keepLastDirectionP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (qAt h k))) := by
  obtain ⟨π, e3, e4⟩ := exists_perm34 h k hk
  obtain ⟨M, hM, rfl⟩ := keepPlaneP'_le h k hX.1
  have hM' : Mᵀ = -M := hM
  obtain ⟨hmem, hcent⟩ := carry_general keepLastDirectionP' keepLastDirectionF' (fun a b _ hY => keepPlaneP'_le a b hY.1)
    (fun a b _ hY => keepPlaneF'_le a b hY.1) transfer_lastDirection keepLastDirection_map π 3 4 M hM'
  rw [e3, e4] at hmem hcent
  have hm0 : SysExt.turnOf tenLine (M.submatrix (tenPerm π) (tenPerm π)) ∈ keepLastDirectionP := by
    rw [← keepLastDirection34P]
    exact hmem.mp hX
  rw [hcent, keepLastDirection34P, pair_lastDirection_centre _ hm0]
  exact centre_finish π M hM' RQ (qAt h k) (by rw [RQ_eq, uFive_diagonal_perm, ← qAt_perm π e3 e4])

/-! ## Proposition 46 -/

/-- **Proposition 46 (the rotations of a pair, and what each keeps).** The ten lines of a pair on `H ⊗ H ⊗ ℂ²`,
`Γ_a = γ_a ⊗ 1 ⊗ σ_x`, `Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y`, anticommute, `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`; the two-spinor states are
`σ_z = +1`, on which the rotations `½Γ_xΓ_y` act as `γ_aγ_b ⊗ 1`, `1 ⊗ γ_aγ_b` and `iγ_a ⊗ γ_b` (times `½`); they span
`so(10)`, dimension 45; `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z` and `e^{−iπL/4} = −iP` on each two-spinor state; the rotations keeping
the comparison are `u(5)`, 25 (keeping `L ⊗ 1` likewise), with centre `ℝ·i(L − 1) ⊗ σ_z`, the rotation
`ρ(J) = ½ i(L − 1) ⊗ σ_z` of the complex structure; keeping also the singlet `Ω ⊗ e₊`: `su(5)`, 24; keeping also the plane
count `N_F = Σ_{t ∈ F}(1 − (γ_t ⊗ γ_t) ⊗ σ_z)/2`: `s(u(3) ⊕ u(2))`, 12, with centre `ℝ·ρ(iY)`; keeping also the last-step direction's
two-spinor state `ℓ_h ⊗ e₊`: `su(3) ⊕ u(1)`, 9, with centre `ℝ·ρ(iQ)` — at every plane `F = {h, k}` with the last-step direction `h`
(`Y = ½` on `F`, `−⅓` on `C`; `Q = 0` on `h`, `1` on `k`, `−⅓` on `C`); `(A, B, z) ↦ (z²A, z̄³B)` maps
`SU(3) × SU(2) × U(1)` onto `S(U(3) × U(2))`, with kernel the six images of the sixth roots of unity, cyclic, and
`(SU(3) × SU(2) × U(1))/ℤ₆ ≃ S(U(3) × U(2))`; and on the sixteen, at every plane, `Tr Y = Tr Y³ = 0` and the colour
and the doublet sums of `Y` vanish (`Tr YT_c² = Tr YT₃² = 0`).

Recognition: the gauge group of the standard model, `S(U(2) × U(3)) = (SU(3) × SU(2) × U(1))/ℤ₆`, twelve
generators, held by `SU(5)`; `Y` the hypercharge, `Q` the electric charge. Uses Props. 4, 10, 11, 21, 45. -/
theorem prop_46 :
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
    (∀ X ∈ keepLP, (∀ Y ∈ keepLP, X * Y = Y * X) ↔ ∃ a : ℝ, X = a • (I • ((L - 1) ⊗ₖ σ₃))) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ X ∈ keepPlaneP' h k, (∀ Y ∈ keepPlaneP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (yAt h k)))) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ X ∈ keepLastDirectionP' h k, (∀ Y ∈ keepLastDirectionP' h k, X * Y = Y * X) ↔
      ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive (Matrix.diagonal (qAt h k)))) ∧
    Nonempty (((GroupsContinuumLaw.SU3 × GroupsContinuumLaw.SU2 × GroupsContinuumLaw.U1) ⧸ GroupsContinuumLaw.symHom.ker) ≃* GroupsContinuumLaw.SU32) ∧
    (∀ h k : Fin 5, h ≠ k → ∑ r, hyper h k r = 0 ∧ ∑ r, hyper h k r ^ 3 = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper h k r = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper h k r = 0) := by
  obtain ⟨c1, c2⟩ := prop_46_chain
  refine ⟨c1, c2, fun a b r => tenLine_on_relations a b r, fun X hX => pair_L_centre X hX,
    fun h k hk X hX => pair_plane_centre_every h k hk X hX, fun h k hk X hX => pair_lastDirection_centre_every h k hk X hX,
    ⟨GroupsContinuumLaw.sym_quotient⟩, fun h k hk => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, -⟩ := (prop_45 h k hk).2.2.2.2.2.2.1
  exact ⟨a1, a2, a3, a4⟩

end Comparison.System.Existence
