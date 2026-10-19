import Comparison.System.Existence.PairModel

/-!
# The proof system, the existence layer: the centres of the pair's rotations (Proposition 46)

The rotation `uFive R` of the ten lines is the real form `[[Re Z, −Im Z], [Im Z, Re Z]]` of the
`5 × 5` matrix `Z = zc R` (`uFive_eq_realForm`); the real form is multiplicative and injective, so two rotations of the
pair commute exactly when their `5 × 5` matrices do (`comm_iff_zMat`). The rotations of the pair that keep the
comparison, the singlet and `N_F` are the `ρ(uFive R)` with `zc R` in `s(u(3) ⊕ u(2))` and every such matrix occurs
(`zMat_plane_iff`); so the centre of `keepPlaneP` is `ℝ·ρ(Y)` and that of `keepLastDirectionP` is `ℝ·ρ(Q)`
(`pair_plane_centre`, `pair_lastDirection_centre`), from `GroupsContinuumLaw.plane_centre`, `lastDirection_centre`.
-/

namespace Comparison.System.Existence

open Matrix Complex

/-- The `5 × 5` matrix of the rotation `uFive R`, `Z = A + iB`. -/
noncomputable def zMat (R : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of (SysExt.zc R)

/-- The real form of `Z`. -/
def realForm (Z : Matrix (Fin 5) (Fin 5) ℂ) : Matrix SysExt.Ten SysExt.Ten ℝ :=
  Matrix.fromBlocks (Z.map Complex.re) (-(Z.map Complex.im)) (Z.map Complex.im) (Z.map Complex.re)

theorem uFive_eq_realForm (R : Matrix (Fin 5) (Fin 5) ℝ) : SysExt.uFive R = realForm (zMat R) := by
  rw [SysExt.uFive_apply, realForm]
  congr 1 <;> ext s t <;> simp [zMat, SysExt.zc]

theorem map_re_mul (Z W : Matrix (Fin 5) (Fin 5) ℂ) :
    (Z * W).map Complex.re = Z.map Complex.re * W.map Complex.re - Z.map Complex.im * W.map Complex.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Complex.re_sum, Complex.mul_re, Matrix.sub_apply,
    Finset.sum_sub_distrib]

theorem map_im_mul (Z W : Matrix (Fin 5) (Fin 5) ℂ) :
    (Z * W).map Complex.im = Z.map Complex.re * W.map Complex.im + Z.map Complex.im * W.map Complex.re := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Matrix.add_apply,
    Finset.sum_add_distrib]

theorem realForm_mul (Z W : Matrix (Fin 5) (Fin 5) ℂ) : realForm (Z * W) = realForm Z * realForm W := by
  rw [realForm, realForm, realForm, Matrix.fromBlocks_multiply, map_re_mul, map_im_mul]
  congr 1 <;> first | noncomm_ring | abel

theorem realForm_sub (Z W : Matrix (Fin 5) (Fin 5) ℂ) : realForm (Z - W) = realForm Z - realForm W := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [realForm] <;> ring

theorem realForm_injective {Z : Matrix (Fin 5) (Fin 5) ℂ} (h : realForm Z = 0) : Z = 0 := by
  rw [realForm, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h
  obtain ⟨h1, -, h3, -⟩ := h
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h3 i) j

theorem zMat_injective {R R' : Matrix (Fin 5) (Fin 5) ℝ} (h : zMat R = zMat R') : R = R' :=
  SysExt.uFive_injective (by rw [uFive_eq_realForm, uFive_eq_realForm, h])

/-- **Two rotations of the pair commute exactly when their `5 × 5` matrices do.** -/
theorem comm_iff_zMat (R R' : Matrix (Fin 5) (Fin 5) ℝ) :
    SysExt.turnOf tenLine (SysExt.uFive R) * SysExt.turnOf tenLine (SysExt.uFive R') =
        SysExt.turnOf tenLine (SysExt.uFive R') * SysExt.turnOf tenLine (SysExt.uFive R) ↔
      zMat R * zMat R' = zMat R' * zMat R := by
  have hlie := SysExt.turnOf_lie tenLine SysExt.tenLine_isTen (SysExt.uFive R) (SysExt.uFive R')
    (SysExt.uFive_mem_skew R)
  have hskew := SysExt.comm_skew _ _ (SysExt.uFive_mem_skew R) (SysExt.uFive_mem_skew R')
  rw [← sub_eq_zero, hlie]
  have hc : SysExt.uFive R * SysExt.uFive R' - SysExt.uFive R' * SysExt.uFive R =
      realForm (zMat R * zMat R' - zMat R' * zMat R) := by
    rw [uFive_eq_realForm, uFive_eq_realForm, realForm_sub, realForm_mul, realForm_mul]
  constructor
  · intro h
    have h0 := SysExt.turnOf_eq_zero tenLine SysExt.tenLine_isTen _ hskew h
    rw [hc] at h0
    exact sub_eq_zero.mp (realForm_injective h0)
  · intro h
    rw [hc, sub_eq_zero.mpr h]
    have : realForm 0 = 0 := by
      rw [realForm]
      simp
    rw [this, map_zero]

/-- The real matrix of `iY`, `diag(−⅓, −⅓, −⅓, ½, ½)`. -/
noncomputable def RY : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![-1 / 3, -1 / 3, -1 / 3, 1 / 2, 1 / 2]

/-- The real matrix of `iQ`, `diag(−⅓, −⅓, −⅓, 0, 1)`. -/
noncomputable def RQ : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![-1 / 3, -1 / 3, -1 / 3, 0, 1]

theorem zMat_diag (d : Fin 5 → ℝ) : zMat (Matrix.diagonal d) = Matrix.diagonal fun s => I * (d s : ℂ) := by
  ext s t
  simp only [zMat, Matrix.of_apply, SysExt.zc, SysExt.skA, SysExt.syB, Matrix.diagonal_apply]
  by_cases h : s = t
  · subst h
    simp
  · rcases lt_or_gt_of_ne h with hst | hst
    · simp [h, hst, not_le.mpr hst, Ne.symm h]
    · simp [h, hst, not_lt.mpr hst.le, le_of_lt hst, Ne.symm h]

theorem zMat_RY : zMat RY = GroupsContinuumLaw.Yc := by
  rw [RY, zMat_diag, GroupsContinuumLaw.Yc]
  congr 1
  funext s
  fin_cases s <;> simp [GroupsContinuumLaw.yv]

theorem zMat_RQ : zMat RQ = GroupsContinuumLaw.Qc := by
  rw [RQ, zMat_diag, GroupsContinuumLaw.Qc]
  congr 1
  funext s
  fin_cases s <;> simp [GroupsContinuumLaw.qv]

theorem crossP_iff : ∀ s t : Fin 5, SysExt.crossP (s, t) ↔ GroupsContinuumLaw.cross5 s t := by
  decide

theorem zMat_apply (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : zMat R s t = SysExt.zc R s t := rfl

theorem zc_re (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : (SysExt.zc R s t).re = SysExt.skA R s t := by
  simp [SysExt.zc]

theorem zc_im (R : Matrix (Fin 5) (Fin 5) ℝ) (s t : Fin 5) : (SysExt.zc R s t).im = SysExt.syB R s t := by
  simp [SysExt.zc]

theorem zMat_antiHerm (R : Matrix (Fin 5) (Fin 5) ℝ) : (zMat R)ᴴ = -zMat R := by
  ext s t
  apply Complex.ext
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_re, Complex.neg_re,
      zMat_apply, zc_re]
    rw [SysExt.skA_swap]
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_im, Complex.neg_im,
      zMat_apply, zc_im]
    rw [SysExt.syB_swap]

theorem zMat_trace (R : Matrix (Fin 5) (Fin 5) ℝ) : (zMat R).trace = I * (R.trace : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, zMat_apply, SysExt.zc_diag]
  rw [← Finset.mul_sum]
  push_cast
  rfl

/-- The real matrix of a `5 × 5` anti-Hermitian `W`: the upper triangle from `Re W`, the rest from `Im W`. -/
noncomputable def realOf (W : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun s t => if s < t then (W s t).re else (W s t).im

theorem zMat_realOf {W : Matrix (Fin 5) (Fin 5) ℂ} (hW : Wᴴ = -W) : zMat (realOf W) = W := by
  have hp : ∀ s t, (W s t).re = -(W t s).re ∧ (W s t).im = (W t s).im := by
    intro s t
    have e := congrFun (congrFun hW t) s
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im] at e1 e2
    exact ⟨by linarith, by linarith⟩
  ext s t
  simp only [zMat, Matrix.of_apply, SysExt.zc, SysExt.skA, SysExt.syB, realOf]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero, zero_sub]
    rcases lt_trichotomy s t with h | rfl | h
    · simp [h]
    · simp only [lt_irrefl, if_false]
      have := (hp s s).1
      linarith
    · simp only [not_lt.mpr h.le, h, if_true, if_false]
      linarith [(hp s t).1]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, zero_add, mul_zero]
    rcases lt_trichotomy s t with h | rfl | h
    · simp only [not_le.mpr h, if_false, not_lt.mpr h.le]
      linarith [(hp s t).2]
    · simp
    · simp only [le_of_lt h, if_true, not_lt.mpr h.le, if_false]

theorem realOf_trace {W : Matrix (Fin 5) (Fin 5) ℂ} : (realOf W).trace = W.trace.im := by
  simp only [Matrix.trace, Matrix.diag, realOf, Matrix.of_apply, lt_irrefl, if_false, Complex.im_sum]

/-- **The plane rotations of the pair are exactly the `ρ(uFive R)` with `zc R` in `s(u(3) ⊕ u(2))`.** -/
theorem zMat_plane_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    R ∈ LinearMap.ker (SysExt.kerP SysExt.crossP) ↔ GroupsContinuumLaw.IsPlaneTurn (zMat R) := by
  rw [SysExt.mem_ker_kerP]
  constructor
  · rintro ⟨htr, hc⟩
    refine ⟨zMat_antiHerm R, by rw [zMat_trace, htr]; simp, fun s t hst => ?_⟩
    exact SysExt.zc_cross (fun s t h => hc (s, t) h) ((crossP_iff s t).mpr hst)
  · rintro ⟨-, htr, hc⟩
    refine ⟨?_, fun p hp => ?_⟩
    · have := congrArg Complex.im htr
      rw [zMat_trace] at this
      simpa using this
    · have h1 := hc p.1 p.2 ((crossP_iff p.1 p.2).mp hp)
      have hre := congrArg Complex.re h1
      have him := congrArg Complex.im h1
      rw [zMat_apply, zc_re, Complex.zero_re] at hre
      rw [zMat_apply, zc_im, Complex.zero_im] at him
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · simpa [SysExt.skA, h] using hre
      · exfalso
        rcases hp with ⟨a, b⟩ | ⟨a, b⟩
        · rw [h] at a
          exact absurd (lt_of_lt_of_le a b) (lt_irrefl _)
        · rw [h] at a
          exact absurd (lt_of_le_of_lt a b) (lt_irrefl _)
      · simpa [SysExt.syB, le_of_lt h] using him

theorem plane_turn_exists (W : Matrix (Fin 5) (Fin 5) ℂ) (hW : GroupsContinuumLaw.IsPlaneTurn W) :
    ∃ R ∈ LinearMap.ker (SysExt.kerP SysExt.crossP), zMat R = W :=
  ⟨realOf W, (zMat_plane_iff _).mpr (by rw [zMat_realOf hW.1]; exact hW), zMat_realOf hW.1⟩

theorem zMat_lastDirection_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    R ∈ LinearMap.ker (SysExt.kerP SysExt.lastDirectionP) ↔ GroupsContinuumLaw.IsLastDirectionTurn (zMat R) := by
  have hface : R ∈ LinearMap.ker (SysExt.kerP SysExt.lastDirectionP) →
      R ∈ LinearMap.ker (SysExt.kerP SysExt.crossP) := by
    intro h
    rw [SysExt.mem_ker_kerP] at h ⊢
    exact ⟨h.1, fun p hp => h.2 p (Or.inl hp)⟩
  constructor
  · intro h
    have hf := (zMat_plane_iff R).mp (hface h)
    rw [SysExt.mem_ker_kerP] at h
    have h33 : R 3 3 = 0 := h.2 (3, 3) (Or.inr (Or.inl rfl))
    have h34 : R 3 4 = 0 := h.2 (3, 4) (Or.inr (Or.inr (Or.inl rfl)))
    have h43 : R 4 3 = 0 := h.2 (4, 3) (Or.inr (Or.inr (Or.inr rfl)))
    refine ⟨hf, ?_, ?_, ?_⟩
    · rw [zMat_apply, SysExt.zc_diag, h33]
      simp
    · apply Complex.ext
      · rw [zMat_apply, zc_re]
        simp [SysExt.skA, h34]
      · rw [zMat_apply, zc_im]
        simp [SysExt.syB, h43]
    · apply Complex.ext
      · rw [zMat_apply, zc_re]
        simp [SysExt.skA, h34]
      · rw [zMat_apply, zc_im]
        simp [SysExt.syB, h43]
  · rintro ⟨hf, z33, z34, -⟩
    have hk := (zMat_plane_iff R).mpr hf
    rw [SysExt.mem_ker_kerP] at hk ⊢
    have e33 := congrArg Complex.im z33
    rw [zMat_apply, SysExt.zc_diag] at e33
    have e34r := congrArg Complex.re z34
    rw [zMat_apply, zc_re] at e34r
    have e34i := congrArg Complex.im z34
    rw [zMat_apply, zc_im] at e34i
    refine ⟨hk.1, fun p hp => ?_⟩
    rcases hp with hp | rfl | rfl | rfl
    · exact hk.2 p hp
    · simpa using e33
    · simpa [SysExt.skA] using e34r
    · simpa [SysExt.syB] using e34i

theorem lastDirection_turn_exists (W : Matrix (Fin 5) (Fin 5) ℂ) (hW : GroupsContinuumLaw.IsLastDirectionTurn W) :
    ∃ R ∈ LinearMap.ker (SysExt.kerP SysExt.lastDirectionP), zMat R = W :=
  ⟨realOf W, (zMat_lastDirection_iff _).mpr (by rw [zMat_realOf hW.1.1]; exact hW), zMat_realOf hW.1.1⟩

/-- **The centre of the pair's `s(u(3) ⊕ u(2))` is `ℝ·ρ(Y)`.** -/
theorem pair_plane_centre (X : PairM) (hX : X ∈ keepPlaneP) :
    (∀ Y ∈ keepPlaneP, X * Y = Y * X) ↔ ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive RY) := by
  rw [keepPlaneP_eq] at hX
  obtain ⟨R, hR, rfl⟩ := hX
  constructor
  · intro hc
    have hcomm : ∀ W, GroupsContinuumLaw.IsPlaneTurn W → zMat R * W = W * zMat R := by
      intro W hW
      obtain ⟨R', hR', rfl⟩ := plane_turn_exists W hW
      have := hc _ (by rw [keepPlaneP_eq]; exact ⟨R', hR', rfl⟩)
      exact (comm_iff_zMat R R').mp this
    obtain ⟨a, ha⟩ := GroupsContinuumLaw.plane_centre (zMat R) ((zMat_plane_iff R).mp hR) hcomm
    refine ⟨a, ?_⟩
    have hRa : R = a • RY := by
      apply zMat_injective
      rw [ha, ← zMat_RY]
      ext s t
      simp only [zMat, Matrix.of_apply, Matrix.smul_apply, SysExt.zc, SysExt.skA, SysExt.syB, smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    change SysExt.turnOf tenLine (SysExt.uFive R) = _
    rw [hRa, map_smul, map_smul]
  · rintro ⟨a, ha⟩ Y hY
    rw [keepPlaneP_eq] at hY
    obtain ⟨R', hR', rfl⟩ := hY
    have hYc := GroupsContinuumLaw.Yc_central (zMat R') ((zMat_plane_iff R').mp hR')
    rw [← zMat_RY] at hYc
    have h := (comm_iff_zMat RY R').mpr hYc
    change SysExt.turnOf tenLine (SysExt.uFive R) * SysExt.turnOf tenLine (SysExt.uFive R') =
      SysExt.turnOf tenLine (SysExt.uFive R') * SysExt.turnOf tenLine (SysExt.uFive R)
    change SysExt.turnOf tenLine (SysExt.uFive R) = _ at ha
    rw [ha, smul_mul_assoc, h, mul_smul_comm]

/-- **The centre of the pair's `su(3) ⊕ u(1)` is `ℝ·ρ(Q)`.** -/
theorem pair_lastDirection_centre (X : PairM) (hX : X ∈ keepLastDirectionP) :
    (∀ Y ∈ keepLastDirectionP, X * Y = Y * X) ↔ ∃ a : ℝ, X = a • SysExt.turnOf tenLine (SysExt.uFive RQ) := by
  rw [keepLastDirectionP_eq] at hX
  obtain ⟨R, hR, rfl⟩ := hX
  constructor
  · intro hc
    have hcomm : ∀ W, GroupsContinuumLaw.IsLastDirectionTurn W → zMat R * W = W * zMat R := by
      intro W hW
      obtain ⟨R', hR', rfl⟩ := lastDirection_turn_exists W hW
      have := hc _ (by rw [keepLastDirectionP_eq]; exact ⟨R', hR', rfl⟩)
      exact (comm_iff_zMat R R').mp this
    obtain ⟨a, ha⟩ := GroupsContinuumLaw.lastDirection_centre (zMat R) ((zMat_lastDirection_iff R).mp hR) hcomm
    refine ⟨a, ?_⟩
    have hRa : R = a • RQ := by
      apply zMat_injective
      rw [ha, ← zMat_RQ]
      ext s t
      simp only [zMat, Matrix.of_apply, Matrix.smul_apply, SysExt.zc, SysExt.skA, SysExt.syB, smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    change SysExt.turnOf tenLine (SysExt.uFive R) = _
    rw [hRa, map_smul, map_smul]
  · rintro ⟨a, ha⟩ Y hY
    rw [keepLastDirectionP_eq] at hY
    obtain ⟨R', hR', rfl⟩ := hY
    have hQc := GroupsContinuumLaw.Qc_central (zMat R') ((zMat_lastDirection_iff R').mp hR')
    rw [← zMat_RQ] at hQc
    have h := (comm_iff_zMat RQ R').mpr hQc
    change SysExt.turnOf tenLine (SysExt.uFive R) * SysExt.turnOf tenLine (SysExt.uFive R') =
      SysExt.turnOf tenLine (SysExt.uFive R') * SysExt.turnOf tenLine (SysExt.uFive R)
    change SysExt.turnOf tenLine (SysExt.uFive R) = _ at ha
    rw [ha, smul_mul_assoc, h, mul_smul_comm]

end Comparison.System.Existence
