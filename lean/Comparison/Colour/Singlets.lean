module

public import Comparison.Colour.Kernel

/-!
# Book XIII. The colour singlets (Proposition 74)

The rotations of the three colour lines
are `SU(3)` (`IsSU3 U`: `U U† = 1`, `det U = 1`), acting on a colour end by `U` and on a conjugate end
by `Ū`, so on `ℂ³ ⊗ ℂ̄³` (a `3 × 3` matrix `X`) by `X ↦ U X U†`, on three ends by `U ⊗ U ⊗ U`.

* `meson_singlet`: **`Inv(ℂ³ ⊗ ℂ̄³) = ℂ·δ`**: `U X U† = X` for every `U ∈ SU(3)` exactly when
  `X = c·1` (three rotations suffice: `diag(−1, −1, 1)`, `diag(−1, 1, −1)` and the cyclic rotation).
* `levi_kept`: `Σ U_ia U_jb U_kc ε_abc = det U · ε_ijk`; `baryon_singlet`: **`Inv(ℂ³⊗ℂ³⊗ℂ³) = ℂ·ε`**
  (four rotations suffice: `diag(i, i, −1)`, `diag(i, −1, i)` and minus two exchanges).
* `no_singlet`: **for `3 ∤ n` the only tensor of `(ℂ³)^{⊗n}` kept by `SU(3)` is `0`**: the centre
  `e^{2πi/3}·1` acts by `e^{2πin/3} ≠ 1`.
* `norm_delta`, `norm_eps`: `|δ|² = 3`, `|ε|² = 6`, so the unit singlets are `δ/√3`, `ε/√6`.
* `hook_values`: `2(3k)!/(k!(k+1)!(k+2)!) = 1, 5, 42, 462` for `k = 1, …, 4`.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex

/-- A rotation of the three colour lines: `U ∈ SU(3)`. -/
def IsSU3 (U : Matrix (Fin 3) (Fin 3) ℂ) : Prop := U ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ

theorem isSU3_of (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U * star U = 1) (hd : U.det = 1) :
    IsSU3 U :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr hU, hd⟩

theorem IsSU3.mul_star {U : Matrix (Fin 3) (Fin 3) ℂ} (h : IsSU3 U) : U * star U = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp h).1

theorem IsSU3.det {U : Matrix (Fin 3) (Fin 3) ℂ} (h : IsSU3 U) : U.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).2

/-! ## Some rotations -/

/-- `diag(−1, −1, 1)`. -/
def turnA : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
/-- `diag(−1, 1, −1)`. -/
def turnB : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
/-- The cyclic rotation of the three lines. -/
def turnCyc : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
/-- `diag(i, i, −1)`. -/
def turnI1 : Matrix (Fin 3) (Fin 3) ℂ := !![I, 0, 0; 0, I, 0; 0, 0, -1]
/-- `diag(i, −1, i)`. -/
def turnI2 : Matrix (Fin 3) (Fin 3) ℂ := !![I, 0, 0; 0, -1, 0; 0, 0, I]
/-- Minus the exchange of the first two lines. -/
def turnX01 : Matrix (Fin 3) (Fin 3) ℂ := !![0, -1, 0; -1, 0, 0; 0, 0, -1]
/-- Minus the exchange of the last two lines. -/
def turnX12 : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, 0, -1; 0, -1, 0]

/-- Check `U U† = 1` entry by entry. -/
macro "su3_unitary" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.star_apply]))

theorem turnA_SU3 : IsSU3 turnA :=
  isSU3_of _ (by unfold turnA; su3_unitary) (by simp [turnA, Matrix.det_fin_three])
theorem turnB_SU3 : IsSU3 turnB :=
  isSU3_of _ (by unfold turnB; su3_unitary) (by simp [turnB, Matrix.det_fin_three])
theorem turnCyc_SU3 : IsSU3 turnCyc :=
  isSU3_of _ (by unfold turnCyc; su3_unitary) (by simp [turnCyc, Matrix.det_fin_three])
theorem turnI1_SU3 : IsSU3 turnI1 :=
  isSU3_of _ (by unfold turnI1; su3_unitary) (by simp [turnI1, Matrix.det_fin_three])
theorem turnI2_SU3 : IsSU3 turnI2 :=
  isSU3_of _ (by unfold turnI2; su3_unitary) (by simp [turnI2, Matrix.det_fin_three])
theorem turnX01_SU3 : IsSU3 turnX01 :=
  isSU3_of _ (by unfold turnX01; su3_unitary) (by simp [turnX01, Matrix.det_fin_three])
theorem turnX12_SU3 : IsSU3 turnX12 :=
  isSU3_of _ (by unfold turnX12; su3_unitary) (by simp [turnX12, Matrix.det_fin_three])

/-- The entries of a product of explicit `3 × 3` matrices. -/
theorem mulEntries (A B : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## A line and its conjugate -/

/-- **`Inv(ℂ³ ⊗ ℂ̄³) = ℂ·δ`:** a line closes with its conjugate in one way. -/
theorem meson_singlet (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (∀ U, IsSU3 U → U * X * star U = X) ↔ ∃ c : ℂ, X = c • 1 := by
  constructor
  · intro h
    have hA := h _ turnA_SU3
    have hB := h _ turnB_SU3
    have hC := h _ turnCyc_SU3
    have e : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ), U * X * star U = X → ∀ i j,
        (U * X * star U) i j = X i j := fun U hU i j => by rw [hU]
    have off : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3), U * X * star U = X →
        (U * X * star U) i j = -X i j → X i j = 0 := by
      intro U i j hU h'
      have := e U hU i j
      rw [h'] at this
      linear_combination (-1 / 2 : ℂ) * this
    have a01 : X 0 1 = 0 :=
      off _ 0 1 hB (by simp only [mulEntries]; simp [turnB, Matrix.star_apply])
    have a10 : X 1 0 = 0 :=
      off _ 1 0 hB (by simp only [mulEntries]; simp [turnB, Matrix.star_apply])
    have a02 : X 0 2 = 0 :=
      off _ 0 2 hA (by simp only [mulEntries]; simp [turnA, Matrix.star_apply])
    have a20 : X 2 0 = 0 :=
      off _ 2 0 hA (by simp only [mulEntries]; simp [turnA, Matrix.star_apply])
    have a12 : X 1 2 = 0 :=
      off _ 1 2 hA (by simp only [mulEntries]; simp [turnA, Matrix.star_apply])
    have a21 : X 2 1 = 0 :=
      off _ 2 1 hA (by simp only [mulEntries]; simp [turnA, Matrix.star_apply])
    have d1 : X 1 1 = X 0 0 := by
      have h' := e _ hC 1 1
      have : (turnCyc * X * star turnCyc) 1 1 = X 0 0 := by
        simp only [mulEntries]
        simp [turnCyc, Matrix.star_apply]
      rw [this] at h'
      exact h'.symm
    have d2 : X 2 2 = X 0 0 := by
      have h' := e _ hC 0 0
      have : (turnCyc * X * star turnCyc) 0 0 = X 2 2 := by
        simp only [mulEntries]
        simp [turnCyc, Matrix.star_apply]
      rw [this] at h'
      exact h'
    refine ⟨X 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a01, a10, a02, a20, a12, a21, d1, d2]
  · rintro ⟨c, rfl⟩ U hU
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU.mul_star]

/-! ## Three lines -/

/-- `U ⊗ U ⊗ U` on three colour ends. -/
def act3 (U : Matrix (Fin 3) (Fin 3) ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun i j k => ∑ a, ∑ b, ∑ c, U i a * U j b * U k c * T a b c

/-- **`Σ U_ia U_jb U_kc ε_abc = det U · ε_ijk`.** -/
theorem levi_kept (U : Matrix (Fin 3) (Fin 3) ℂ) : act3 U epsT = U.det • epsT := by
  ext i j k
  simp only [act3, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_three, epsT, Matrix.det_fin_three] <;> ring

theorem act3_diag (z : Fin 3 → ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (i j k : Fin 3) :
    act3 (Matrix.diagonal z) T i j k = z i * z j * z k * T i j k := by
  rw [act3]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem turnI1_eq : turnI1 = Matrix.diagonal ![I, I, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnI1]

theorem turnI2_eq : turnI2 = Matrix.diagonal ![I, -1, I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnI2]

/-- A kept tensor vanishes where a diagonal rotation moves its phase. -/
theorem zero_of_phase (z : Fin 3 → ℂ) (T : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (h : act3 (Matrix.diagonal z) T = T) (i j k : Fin 3) (hp : z i * z j * z k ≠ 1) :
    T i j k = 0 := by
  have e := congrFun (congrFun (congrFun h i) j) k
  rw [act3_diag] at e
  have : (z i * z j * z k - 1) * T i j k = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hp
  · exact h0

set_option linter.unusedTactic false in
-- `done` closes the alternatives of `first` that leave a goal
/-- **`Inv(ℂ³ ⊗ ℂ³ ⊗ ℂ³) = ℂ·ε`:** three lines close in one way. -/
theorem baryon_singlet (T : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∀ U, IsSU3 U → act3 U T = T) ↔ ∃ c : ℂ, T = c • epsT := by
  constructor
  · intro h
    have h1 := h _ turnI1_SU3
    have h2 := h _ turnI2_SU3
    rw [turnI1_eq] at h1
    rw [turnI2_eq] at h2
    have x01 := h _ turnX01_SU3
    have x12 := h _ turnX12_SU3
    have e : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ), act3 U T = T → ∀ i j k,
        act3 U T i j k = T i j k := fun U hU i j k => by rw [hU]
    have flip : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) (i j k : Fin 3) (x : ℂ), act3 U T = T →
        act3 U T i j k = -x → T i j k = -x := by
      intro U i j k x hU h'
      rw [← e U hU i j k, h']
    have r1 : T 0 1 2 = -T 1 0 2 :=
      flip _ 0 1 2 _ x01 (by simp [act3, turnX01, Fin.sum_univ_three])
    have r2 : T 0 1 2 = -T 0 2 1 :=
      flip _ 0 1 2 _ x12 (by simp [act3, turnX12, Fin.sum_univ_three])
    have r3 : T 0 2 1 = -T 1 2 0 :=
      flip _ 0 2 1 _ x01 (by simp [act3, turnX01, Fin.sum_univ_three])
    have r4 : T 1 0 2 = -T 2 0 1 :=
      flip _ 1 0 2 _ x12 (by simp [act3, turnX12, Fin.sum_univ_three])
    have r5 : T 2 0 1 = -T 2 1 0 :=
      flip _ 2 0 1 _ x01 (by simp [act3, turnX01, Fin.sum_univ_three])
    refine ⟨T 0 1 2, ?_⟩
    ext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, epsT] <;> norm_num <;>
      first
        | (apply zero_of_phase _ T h1; simp [Complex.ext_iff]; done)
        | (apply zero_of_phase _ T h2; simp [Complex.ext_iff]; done)
        | linear_combination r1 | linear_combination r2
        | linear_combination r3 - r2 | linear_combination r4 - r1
        | linear_combination r5 - r4 + r1
  · rintro ⟨c, rfl⟩ U hU
    ext i j k
    have := congrFun (congrFun (congrFun (levi_kept U) i) j) k
    simp only [act3, Pi.smul_apply, smul_eq_mul, hU.det, one_mul] at this ⊢
    rw [← this]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => ?_
    ring

/-! ## No singlet unless three divides the number of lines -/

/-- `U^{⊗n}` on `n` colour ends. -/
def actN (n : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (T : (Fin n → Fin 3) → ℂ) : (Fin n → Fin 3) → ℂ :=
  fun i => ∑ a : Fin n → Fin 3, (∏ m, U (i m) (a m)) * T a

/-- The centre of `SU(3)`: `e^{2πi/3}`. -/
noncomputable def ω3 : ℂ := Complex.exp (2 * Real.pi * I / (3 : ℕ))

theorem ω3_primitive : IsPrimitiveRoot ω3 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem centre_SU3 : IsSU3 (ω3 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  have h3 : ω3 ^ 3 = 1 := ω3_primitive.pow_eq_one
  have hn : ‖ω3‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num)
  have hconj : ω3 * star ω3 = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  refine isSU3_of _ ?_ ?_
  · rw [star_smul, star_one, smul_mul_smul_comm, Matrix.one_mul, hconj, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, h3]

theorem actN_centre (n : ℕ) (c : ℂ) (T : (Fin n → Fin 3) → ℂ) :
    actN n (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) T = c ^ n • T := by
  ext i
  simp only [actN, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.smul_apply, Finset.prod_const, Finset.card_univ]
  · intro a _ ha
    have : ∃ m, i m ≠ a m := by
      by_contra hc
      exact ha (funext fun m => (not_not.mp fun hm => hc ⟨m, hm⟩).symm)
    obtain ⟨m, hm⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ m) (by simp [Matrix.smul_apply, hm]),
      zero_mul]
  · simp

/-- **Lines alone close only in threes:** for `3 ∤ n`, a tensor of `(ℂ³)^{⊗n}` kept by every rotation of
`SU(3)` is zero. -/
theorem no_singlet (n : ℕ) (hn : ¬ 3 ∣ n) (T : (Fin n → Fin 3) → ℂ)
    (h : ∀ U, IsSU3 U → actN n U T = T) : T = 0 := by
  have e := h _ centre_SU3
  rw [actN_centre] at e
  have hne : ω3 ^ n ≠ 1 := fun h1 => hn ((ω3_primitive.pow_eq_one_iff_dvd n).mp h1)
  ext i
  have ei := congrFun e i
  simp only [Pi.smul_apply, smul_eq_mul] at ei
  have : (ω3 ^ n - 1) * T i = 0 := by linear_combination ei
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · simpa using h0

/-! ## The unit singlets and the multiplicities -/

/-- **`|δ|² = Tr 1 = 3`.** -/
theorem norm_delta : ∑ p, star (deltaVec p) * deltaVec p = 3 := by
  simp [deltaVec, Fintype.sum_prod_type]

/-- **`|ε|² = 3! = 6`.** -/
theorem norm_eps : ∑ a, ∑ b, ∑ c, star (epsT a b c) * epsT a b c = 6 := by
  simp [epsT, Fin.sum_univ_three]
  norm_num

/-- **The hook formula for the shape `(k, k, k)`:** `2(3k)!/(k!(k+1)!(k+2)!) = 1, 5, 42, 462`. -/
theorem hook_values :
    (List.range 4).map (fun k => 2 * (3 * (k + 1)).factorial /
      ((k + 1).factorial * (k + 2).factorial * (k + 3).factorial)) = [1, 5, 42, 462] := by
  decide

end Comparison

end
