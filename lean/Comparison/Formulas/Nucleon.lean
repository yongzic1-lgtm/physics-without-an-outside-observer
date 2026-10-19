import Mathlib

/-!
# The nucleon projected (Prop. S120a; formula (54))

Proposition S120a. Each of the three colour lines carries
`V = ℂ²_spin ⊗ ℂ²_isospin`; `V^{⊗3}` is written with the three spins first and the three isospins
second, `(ℂ²)^{⊗3} ⊗ (ℂ²)^{⊗3}`, indexed by `Sp × Sp`, `Sp = Fin 3 → Fin 2` (`0` is up). A permutation
`π` of the three lines acts by `U_π = R_π ⊗ R_π`, `(R_π)_{s s'} = [s' = s ∘ π]`; the total spin is
`S² = S_z² + (S₊S₋ + S₋S₊)/2` on the spins (`S2`), `I²` the same on the isospins.

The whole proof is reduced to eight-dimensional integer facts on the spins of three lines
(`decide +kernel`): `4S² = 3 + 4T` with `T` the three swaps (`casimirZ`), `T² = 3T` (`transZ_sq`),
`T` and `S_z` commute with every `R_π`, and `(3 − T)(S_z² − 1/4) = 0` (`doubletZ`); the rest is the
algebra of `⊗ₖ` and the group sum.

* `Psym_idem`, `trace_Psym`, `rank_Psym`: **`P_sym = (1/6)Σ_π U_π` is a projector of rank 20.**
* `PN_eq`: `P_N = P_sym(15/4 − S²)/3 = P_sym((3 − T) ⊗ 1)/3`; `PN_idem`, `trace_PN`, `rank_PN`,
  `Psym_PN`: **`P_N` is a projector of rank 4 inside the symmetric twenty**; `S2_PN`, `I2_PN`:
  **`S²P_N = I²P_N = (3/4)P_N`**.
* `Pp_idem`, `trace_Pp`, `rank_Pp`: **`P_{p↑} = P_N(S_z + 1/2)(I_z + 1/2)` is a projector of rank one**;
  `charge_Pp`: **`Tr P_{p↑}(I_z + 1/2) = 1`**; `axial_Pp`:
  **`Tr P_{p↑} Σ_r σ_z^{(r)} τ_z^{(r)} = ⟨p↑|Σ_r σ_zτ_z|p↑⟩ = 5/3`**.
* `rank_eq_trace`: an idempotent rational matrix has rank equal to its trace.
-/

namespace Comparison.Formulas.Nucleon

open Matrix Kronecker

set_option maxRecDepth 100000

/-- The spins (or the isospins) of the three colour lines; `0` is up. -/
abbrev Sp := Fin 3 → Fin 2

/-! ## Three lines, over `ℤ` -/

/-- A permutation of the three lines: `(R_π)_{s s'} = [s' = s ∘ π]`. -/
def permZ (π : Equiv.Perm (Fin 3)) : Matrix Sp Sp ℤ :=
  Matrix.of fun s s' => if s' = s ∘ π then 1 else 0

/-- `σ_z` on the line `r`. -/
def szZ (r : Fin 3) : Matrix Sp Sp ℤ := Matrix.diagonal fun s => if s r = 0 then 1 else -1

/-- `σ₊` on the line `r` (down to up). -/
def splusZ (r : Fin 3) : Matrix Sp Sp ℤ :=
  Matrix.of fun s s' => if s' r = 1 ∧ s = Function.update s' r 0 then 1 else 0

/-- `σ₋` on the line `r` (up to down). -/
def sminusZ (r : Fin 3) : Matrix Sp Sp ℤ :=
  Matrix.of fun s s' => if s' r = 0 ∧ s = Function.update s' r 1 then 1 else 0

/-- The three swaps of two lines, summed. -/
def transZ : Matrix Sp Sp ℤ :=
  permZ (Equiv.swap 0 1) + permZ (Equiv.swap 0 2) + permZ (Equiv.swap 1 2)

/-- `2S_z`. -/
def sz2Z : Matrix Sp Sp ℤ := szZ 0 + szZ 1 + szZ 2

/-- `S₊`. -/
def spZ : Matrix Sp Sp ℤ := splusZ 0 + splusZ 1 + splusZ 2

/-- `S₋`. -/
def smZ : Matrix Sp Sp ℤ := sminusZ 0 + sminusZ 1 + sminusZ 2

/-- `2(S_z + 1/2)`. -/
def d2Z : Matrix Sp Sp ℤ := sz2Z + 1

/-- `3 − T`. -/
def c3Z : Matrix Sp Sp ℤ := 3 • 1 - transZ

theorem permZ_mul (π σ : Equiv.Perm (Fin 3)) : permZ π * permZ σ = permZ (π * σ) := by
  ext s s''
  simp only [Matrix.mul_apply, permZ, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.Perm.coe_mul]
  rfl

/-- **`4S² = 3 + 4T`** on the spins of three lines (Dirac's exchange identity summed). -/
theorem casimirZ : sz2Z * sz2Z + 2 • (spZ * smZ + smZ * spZ) = 3 • 1 + 4 • transZ := by
  decide +kernel

/-- **`T² = 3T`**: three spins one half carry no totally antisymmetric part. -/
theorem transZ_sq : transZ * transZ = 3 • transZ := by
  decide +kernel

theorem perm_transZ : ∀ π : Equiv.Perm (Fin 3), permZ π * transZ = transZ * permZ π := by
  decide +kernel

theorem perm_d2Z : ∀ π : Equiv.Perm (Fin 3), permZ π * d2Z = d2Z * permZ π := by
  decide +kernel

theorem trans_d2Z : transZ * d2Z = d2Z * transZ := by
  decide +kernel

/-- **`(3 − T)(S_z² − 1/4) = 0`**, doubled: on spin one half `S_z = ±1/2`. -/
theorem doubletZ : c3Z * (d2Z * d2Z) = 2 • (c3Z * d2Z) := by
  decide +kernel

theorem perm_c3Z : ∀ π : Equiv.Perm (Fin 3), permZ π * c3Z = c3Z * permZ π := by
  decide +kernel

theorem c3_d2Z : c3Z * d2Z = d2Z * c3Z := by
  decide +kernel

theorem c3_sqZ : c3Z * c3Z = 3 • c3Z := by
  decide +kernel

theorem trans_c3Z : transZ * c3Z = 0 := by
  decide +kernel

theorem sum_trace_one : (∑ π : Equiv.Perm (Fin 3), (permZ π).trace * (permZ π).trace) = 120 := by
  decide +kernel

theorem sum_trace_PN :
    (∑ π : Equiv.Perm (Fin 3), (permZ π * c3Z).trace * (permZ π).trace) = 72 := by
  decide +kernel

theorem sum_trace_Pp :
    (∑ π : Equiv.Perm (Fin 3), (permZ π * (c3Z * d2Z)).trace * (permZ π * d2Z).trace) = 72 := by
  decide +kernel

theorem sum_trace_charge :
    (∑ π : Equiv.Perm (Fin 3),
      (permZ π * (c3Z * d2Z)).trace * (permZ π * (d2Z * d2Z)).trace) = 144 := by
  decide +kernel

theorem sum_trace_axial :
    (∑ r : Fin 3, ∑ π : Equiv.Perm (Fin 3),
      (permZ π * (c3Z * d2Z * szZ r)).trace * (permZ π * (d2Z * szZ r)).trace) = 120 := by
  decide +kernel

/-! ## Over `ℚ` -/

/-- The rational matrices of the integer ones. -/
abbrev toQ : Matrix Sp Sp ℤ →+* Matrix Sp Sp ℚ := (Int.castRingHom ℚ).mapMatrix

theorem trace_toQ (M : Matrix Sp Sp ℤ) : (toQ M).trace = (M.trace : ℚ) := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  simp

/-- `R_π`. -/
def R (π : Equiv.Perm (Fin 3)) : Matrix Sp Sp ℚ := toQ (permZ π)

/-- The three swaps `T`. -/
def T : Matrix Sp Sp ℚ := toQ transZ

/-- `3 − T`. -/
def C3 : Matrix Sp Sp ℚ := toQ c3Z

/-- `S_z = (1/2)Σ_r σ_z^{(r)}`. -/
def Sz : Matrix Sp Sp ℚ := (1 / 2 : ℚ) • toQ sz2Z

/-- `S²= S_z² + (S₊S₋ + S₋S₊)/2`. -/
def S2 : Matrix Sp Sp ℚ := Sz * Sz + (1 / 2 : ℚ) • (toQ spZ * toQ smZ + toQ smZ * toQ spZ)

/-- `S_z + 1/2`. -/
def Dq : Matrix Sp Sp ℚ := Sz + (1 / 2 : ℚ) • 1

/-- `σ_z` on the line `r`. -/
def sz (r : Fin 3) : Matrix Sp Sp ℚ := toQ (szZ r)

theorem R_mul (π σ : Equiv.Perm (Fin 3)) : R π * R σ = R (π * σ) := by
  rw [R, R, R, ← map_mul, permZ_mul]

theorem C3_eq : C3 = (3 : ℚ) • 1 - T := by
  rw [C3, c3Z, map_sub, map_nsmul, map_one, T]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  norm_num

theorem Dq_eq : Dq = (1 / 2 : ℚ) • toQ d2Z := by
  rw [Dq, Sz, d2Z, map_add, map_one, smul_add]

/-- **`S² = 3/4 + T`.** -/
theorem S2_eq : S2 = (3 / 4 : ℚ) • 1 + T := by
  have h := congrArg toQ casimirZ
  simp only [map_add, map_mul, map_nsmul, map_one] at h
  simp only [← Nat.cast_smul_eq_nsmul ℚ] at h
  have h' := eq_sub_of_add_eq h
  rw [S2, Sz, T, smul_mul_smul_comm, h']
  push_cast
  module

theorem T_sq : T * T = (3 : ℚ) • T := by
  have h := congrArg toQ transZ_sq
  rw [map_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
  exact_mod_cast h

theorem R_T (π : Equiv.Perm (Fin 3)) : R π * T = T * R π := by
  rw [R, T, ← map_mul, perm_transZ, map_mul]

theorem R_C3 (π : Equiv.Perm (Fin 3)) : R π * C3 = C3 * R π := by
  rw [R, C3, ← map_mul, perm_c3Z, map_mul]

theorem R_Dq (π : Equiv.Perm (Fin 3)) : R π * Dq = Dq * R π := by
  rw [Dq_eq, Matrix.mul_smul, Matrix.smul_mul, R, ← map_mul, perm_d2Z, map_mul]

theorem R_S2 (π : Equiv.Perm (Fin 3)) : R π * S2 = S2 * R π := by
  rw [S2_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, R_T]

theorem C3_sq : C3 * C3 = (3 : ℚ) • C3 := by
  have h := congrArg toQ c3_sqZ
  rw [map_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
  exact_mod_cast h

theorem T_C3 : T * C3 = 0 := by
  rw [T, C3, ← map_mul, trans_c3Z, map_zero]

theorem S2_C3 : S2 * C3 = (3 / 4 : ℚ) • C3 := by
  rw [S2_eq, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, T_C3, add_zero]

theorem C3_Dq : C3 * Dq = Dq * C3 := by
  rw [Dq_eq, C3, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, c3_d2Z]

/-- On spin one half `S_z² = 1/4`: `(3 − T)(S_z + 1/2)² = (3 − T)(S_z + 1/2)`. -/
theorem C3_Dq_sq : C3 * (Dq * Dq) = C3 * Dq := by
  have h := congrArg toQ doubletZ
  rw [map_mul, map_mul, map_nsmul, map_mul, ← Nat.cast_smul_eq_nsmul ℚ] at h
  rw [Dq_eq, smul_mul_smul_comm, Matrix.mul_smul, Matrix.mul_smul, C3, h, smul_smul]
  norm_num

/-! ## The sixty-four states of three lines -/

/-- The three lines' spins and isospins. -/
abbrev Sp2 := Sp × Sp

/-- `U_π = R_π ⊗ R_π`, the permutation of the three lines. -/
def U (π : Equiv.Perm (Fin 3)) : Matrix Sp2 Sp2 ℚ := R π ⊗ₖ R π

/-- **`P_sym = (1/6) Σ_π U_π`.** -/
def Psym : Matrix Sp2 Sp2 ℚ := (1 / 6 : ℚ) • ∑ π, U π

/-- `S²`, `I²`, `S_z`, `I_z` on the sixty-four. -/
def Ssq : Matrix Sp2 Sp2 ℚ := S2 ⊗ₖ (1 : Matrix Sp Sp ℚ)
def Isq : Matrix Sp2 Sp2 ℚ := (1 : Matrix Sp Sp ℚ) ⊗ₖ S2
def Szf : Matrix Sp2 Sp2 ℚ := Sz ⊗ₖ (1 : Matrix Sp Sp ℚ)
def Izf : Matrix Sp2 Sp2 ℚ := (1 : Matrix Sp Sp ℚ) ⊗ₖ Sz

/-- **The nucleon:** `P_N = P_sym(15/4 − S²)/3`. -/
def PN : Matrix Sp2 Sp2 ℚ := (1 / 3 : ℚ) • (Psym * ((15 / 4 : ℚ) • 1 - Ssq))

/-- **The proton with spin up:** `P_{p↑} = P_N(S_z + 1/2)(I_z + 1/2)`. -/
def Pp : Matrix Sp2 Sp2 ℚ := PN * (Szf + (1 / 2 : ℚ) • 1) * (Izf + (1 / 2 : ℚ) • 1)

/-- **The axial current** `Σ_r σ_z^{(r)} τ_z^{(r)}`. -/
def axial : Matrix Sp2 Sp2 ℚ := ∑ r, sz r ⊗ₖ sz r

theorem U_mul (π σ : Equiv.Perm (Fin 3)) : U π * U σ = U (π * σ) := by
  rw [U, U, U, ← Matrix.mul_kronecker_mul, R_mul]

theorem card_perm3 : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- **`P_sym` is a projector.** -/
theorem Psym_idem : Psym * Psym = Psym := by
  have hs : ∀ π : Equiv.Perm (Fin 3), ∑ σ, U (π * σ) = ∑ σ, U σ := fun π =>
    Fintype.sum_equiv (Equiv.mulLeft π) (fun σ => U (π * σ)) U (fun σ => rfl)
  rw [Psym, smul_mul_smul_comm, Finset.sum_mul_sum]
  simp_rw [U_mul]
  rw [Finset.sum_congr rfl (fun π _ => hs π), Finset.sum_const, card_perm3,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num

/-- `P_sym (X ⊗ Y) = (1/6) Σ_π (R_π X) ⊗ (R_π Y)`. -/
theorem Psym_kron (X Y : Matrix Sp Sp ℚ) :
    Psym * (X ⊗ₖ Y) = (1 / 6 : ℚ) • ∑ π, (R π * X) ⊗ₖ (R π * Y) := by
  rw [Psym, Matrix.smul_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [U, ← Matrix.mul_kronecker_mul]

theorem trace_Psym_kron (X Y : Matrix Sp Sp ℚ) :
    (Psym * (X ⊗ₖ Y)).trace = (1 / 6 : ℚ) * ∑ π, (R π * X).trace * (R π * Y).trace := by
  rw [Psym_kron, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp only [Matrix.trace_kronecker]

/-- `X ⊗ Y` commutes with `P_sym` when `X` and `Y` commute with every `R_π`. -/
theorem kron_comm_Psym (X Y : Matrix Sp Sp ℚ) (hX : ∀ π, R π * X = X * R π)
    (hY : ∀ π, R π * Y = Y * R π) : (X ⊗ₖ Y) * Psym = Psym * (X ⊗ₖ Y) := by
  rw [Psym, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [U, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX π, hY π]

/-- **The swaps of two lines read the same on the spins as on the isospins of a symmetric state:**
`P_sym (R_τ ⊗ 1) = P_sym (1 ⊗ R_τ)` for `τ² = 1`. -/
theorem Psym_swap (τ : Equiv.Perm (Fin 3)) (hτ : τ * τ = 1) :
    Psym * (R τ ⊗ₖ (1 : Matrix Sp Sp ℚ)) = Psym * ((1 : Matrix Sp Sp ℚ) ⊗ₖ R τ) := by
  rw [Psym_kron, Psym_kron]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun π => ?_)
  simp only [Equiv.coe_mulRight, Matrix.mul_one, R_mul, mul_assoc, hτ, mul_one]

theorem Psym_T : Psym * (T ⊗ₖ (1 : Matrix Sp Sp ℚ)) = Psym * ((1 : Matrix Sp Sp ℚ) ⊗ₖ T) := by
  have hT : T = R (Equiv.swap 0 1) + R (Equiv.swap 0 2) + R (Equiv.swap 1 2) := by
    rw [T, transZ, map_add, map_add, R, R, R]
  rw [hT]
  simp only [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.mul_add]
  rw [Psym_swap _ (Equiv.swap_mul_self 0 1), Psym_swap _ (Equiv.swap_mul_self 0 2),
    Psym_swap _ (Equiv.swap_mul_self 1 2)]

theorem sub_kron (A B C : Matrix Sp Sp ℚ) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [sub_mul]

theorem kron_sub (A B C : Matrix Sp Sp ℚ) : C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [mul_sub]

theorem Psym_C3 : Psym * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) = Psym * ((1 : Matrix Sp Sp ℚ) ⊗ₖ C3) := by
  rw [C3_eq, sub_kron, kron_sub, Matrix.mul_sub, Matrix.mul_sub, Psym_T,
    Matrix.smul_kronecker, Matrix.kronecker_smul]

theorem one_comm (π : Equiv.Perm (Fin 3)) : R π * (1 : Matrix Sp Sp ℚ) = 1 * R π := by
  rw [Matrix.mul_one, Matrix.one_mul]

theorem kron_one_mul (A B : Matrix Sp Sp ℚ) :
    (A ⊗ₖ (1 : Matrix Sp Sp ℚ)) * (B ⊗ₖ (1 : Matrix Sp Sp ℚ)) = (A * B) ⊗ₖ (1 : Matrix Sp Sp ℚ) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-! ## The nucleon -/

/-- **`P_N = P_sym((3 − T) ⊗ 1)/3`.** -/
theorem PN_eq : PN = (1 / 3 : ℚ) • (Psym * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ))) := by
  rw [PN, Ssq]
  congr 2
  simp only [C3_eq, S2_eq, sub_kron, Matrix.add_kronecker, Matrix.smul_kronecker,
    Matrix.one_kronecker_one]
  module

theorem C3_comm_Psym : (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) * Psym = Psym * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) :=
  kron_comm_Psym _ _ R_C3 one_comm

/-- **`P_N` is a projector.** -/
theorem PN_idem : PN * PN = PN := by
  rw [PN_eq, smul_mul_smul_comm]
  have e : Psym * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) * (Psym * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ))) =
      Psym * ((C3 * C3) ⊗ₖ (1 : Matrix Sp Sp ℚ)) := by
    rw [mul_assoc, ← mul_assoc (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)), C3_comm_Psym, mul_assoc, ← mul_assoc,
      Psym_idem, kron_one_mul]
  rw [e, C3_sq, Matrix.smul_kronecker, Matrix.mul_smul, smul_smul]
  norm_num

/-- **The nucleon lies in the symmetric space:** `P_sym P_N = P_N`. -/
theorem Psym_PN : Psym * PN = PN := by
  rw [PN_eq, Matrix.mul_smul, ← mul_assoc, Psym_idem]

/-- **`S² P_N = (3/4) P_N`.** -/
theorem S2_PN : Ssq * PN = (3 / 4 : ℚ) • PN := by
  have hc : Ssq * Psym = Psym * Ssq := kron_comm_Psym _ _ R_S2 one_comm
  rw [PN_eq, Matrix.mul_smul, ← mul_assoc, hc, mul_assoc, Ssq, kron_one_mul, S2_C3,
    Matrix.smul_kronecker, Matrix.mul_smul, smul_comm]

/-- **`I² P_N = (3/4) P_N`.** -/
theorem I2_PN : Isq * PN = (3 / 4 : ℚ) • PN := by
  have hc : Isq * Psym = Psym * Isq := kron_comm_Psym _ _ one_comm R_S2
  have hT : Psym * ((1 : Matrix Sp Sp ℚ) ⊗ₖ T) * (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) = 0 := by
    rw [← Psym_T, mul_assoc, kron_one_mul, T_C3, Matrix.zero_kronecker, Matrix.mul_zero]
  rw [PN_eq, Matrix.mul_smul, ← mul_assoc, hc, Isq, S2_eq, Matrix.kronecker_add,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, Matrix.mul_add, Matrix.add_mul, hT, add_zero,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_comm]

/-! ## Traces and ranks -/

/-- **An idempotent rational matrix has rank equal to its trace.** -/
theorem rank_eq_trace {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℚ) (h : P * P = P) :
    (P.rank : ℚ) = P.trace := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq] at ht
  rw [ht, Matrix.rank, Matrix.toLin'_apply']

theorem trace_R_mul (π : Equiv.Perm (Fin 3)) (M : Matrix Sp Sp ℤ) :
    (R π * toQ M).trace = ((permZ π * M).trace : ℚ) := by
  rw [R, ← map_mul, trace_toQ]

/-- **`Tr P_sym = 20`.** -/
theorem trace_Psym : Psym.trace = 20 := by
  have h := trace_Psym_kron (1 : Matrix Sp Sp ℚ) 1
  rw [Matrix.one_kronecker_one, Matrix.mul_one] at h
  rw [h]
  simp only [Matrix.mul_one]
  have e : ∀ π : Equiv.Perm (Fin 3), (R π).trace * (R π).trace =
      (((permZ π).trace * (permZ π).trace : ℤ) : ℚ) := by
    intro π
    rw [R, trace_toQ, Int.cast_mul]
  simp only [e]
  rw [← Int.cast_sum, sum_trace_one]
  norm_num

/-- **The symmetric space of three lines has dimension twenty.** -/
theorem rank_Psym : Psym.rank = 20 := by
  have h := rank_eq_trace Psym Psym_idem
  rw [trace_Psym] at h
  exact_mod_cast h

/-- **`Tr P_N = 4`.** -/
theorem trace_PN : PN.trace = 4 := by
  rw [PN_eq, Matrix.trace_smul, trace_Psym_kron, smul_eq_mul]
  have e : ∀ π : Equiv.Perm (Fin 3), (R π * C3).trace * (R π * 1).trace =
      (((permZ π * c3Z).trace * (permZ π).trace : ℤ) : ℚ) := by
    intro π
    rw [C3, trace_R_mul, Matrix.mul_one, R, trace_toQ, Int.cast_mul]
  simp only [e]
  rw [← Int.cast_sum, sum_trace_PN]
  norm_num

/-- **The nucleon: four states.** -/
theorem rank_PN : PN.rank = 4 := by
  have h := rank_eq_trace PN PN_idem
  rw [trace_PN] at h
  exact_mod_cast h

/-! ## The proton with spin up -/

theorem Szf_half : Szf + (1 / 2 : ℚ) • (1 : Matrix Sp2 Sp2 ℚ) = Dq ⊗ₖ (1 : Matrix Sp Sp ℚ) := by
  rw [Szf, Dq, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]

theorem Izf_half : Izf + (1 / 2 : ℚ) • (1 : Matrix Sp2 Sp2 ℚ) = (1 : Matrix Sp Sp ℚ) ⊗ₖ Dq := by
  rw [Izf, Dq, Matrix.kronecker_add, Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- `P_{p↑} = P_sym(((3 − T)(S_z + 1/2)) ⊗ (I_z + 1/2))/3`. -/
theorem Pp_eq : Pp = (1 / 3 : ℚ) • (Psym * ((C3 * Dq) ⊗ₖ Dq)) := by
  rw [Pp, Szf_half, Izf_half, PN_eq, Matrix.smul_mul, Matrix.smul_mul, mul_assoc, mul_assoc,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]

theorem CD_comm (π : Equiv.Perm (Fin 3)) : R π * (C3 * Dq) = C3 * Dq * R π := by
  rw [← mul_assoc, R_C3, mul_assoc, R_Dq, mul_assoc]

/-- **`P_{p↑}` is a projector.** -/
theorem Pp_idem : Pp * Pp = Pp := by
  have hc : ((C3 * Dq) ⊗ₖ Dq) * Psym = Psym * ((C3 * Dq) ⊗ₖ Dq) :=
    kron_comm_Psym _ _ CD_comm R_Dq
  have hsq : (C3 * Dq) * (C3 * Dq) = (3 : ℚ) • (C3 * (Dq * Dq)) := by
    rw [mul_assoc, ← mul_assoc Dq C3 Dq, ← C3_Dq, mul_assoc C3 Dq Dq, ← mul_assoc C3 C3, C3_sq,
      Matrix.smul_mul]
  -- move the isospin square through the swap of the two readings of `3 − T`
  have hiso : Psym * ((C3 * Dq) ⊗ₖ (Dq * Dq)) = Psym * ((C3 * Dq) ⊗ₖ Dq) := by
    have e1 : (C3 * Dq) ⊗ₖ (Dq * Dq) = (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) * (Dq ⊗ₖ (Dq * Dq)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have e2 : (C3 * Dq) ⊗ₖ Dq = (C3 ⊗ₖ (1 : Matrix Sp Sp ℚ)) * (Dq ⊗ₖ Dq) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [e1, e2, ← mul_assoc, ← mul_assoc, Psym_C3, mul_assoc, mul_assoc, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, C3_Dq_sq]
  have hXX : ((C3 * Dq) ⊗ₖ Dq) * ((C3 * Dq) ⊗ₖ Dq) = (3 : ℚ) • ((C3 * Dq) ⊗ₖ (Dq * Dq)) := by
    rw [← Matrix.mul_kronecker_mul, hsq, C3_Dq_sq, Matrix.smul_kronecker]
  have hmain : Psym * ((C3 * Dq) ⊗ₖ Dq) * (Psym * ((C3 * Dq) ⊗ₖ Dq)) =
      (3 : ℚ) • (Psym * ((C3 * Dq) ⊗ₖ Dq)) := by
    rw [mul_assoc, ← mul_assoc ((C3 * Dq) ⊗ₖ Dq) Psym ((C3 * Dq) ⊗ₖ Dq), hc,
      mul_assoc Psym ((C3 * Dq) ⊗ₖ Dq) ((C3 * Dq) ⊗ₖ Dq), ← mul_assoc Psym Psym, Psym_idem, hXX,
      Matrix.mul_smul, hiso]
  rw [Pp_eq, smul_mul_smul_comm, hmain, smul_smul]
  norm_num

theorem trace_Dq_mul (π : Equiv.Perm (Fin 3)) (M : Matrix Sp Sp ℤ) :
    (R π * (toQ M * Dq)).trace = (1 / 2 : ℚ) * ((permZ π * (M * d2Z)).trace : ℚ) := by
  rw [Dq_eq, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← map_mul,
    trace_R_mul]

theorem trace_R_Dq (π : Equiv.Perm (Fin 3)) :
    (R π * Dq).trace = (1 / 2 : ℚ) * ((permZ π * d2Z).trace : ℚ) := by
  rw [Dq_eq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_R_mul]

/-- **`Tr P_{p↑} = 1`.** -/
theorem trace_Pp : Pp.trace = 1 := by
  rw [Pp_eq, Matrix.trace_smul, trace_Psym_kron, smul_eq_mul]
  have e : ∀ π : Equiv.Perm (Fin 3), (R π * (C3 * Dq)).trace * (R π * Dq).trace =
      (1 / 4 : ℚ) * (((permZ π * (c3Z * d2Z)).trace * (permZ π * d2Z).trace : ℤ) : ℚ) := by
    intro π
    rw [C3, trace_Dq_mul, trace_R_Dq]
    push_cast
    ring
  simp only [e, ← Finset.mul_sum]
  rw [← Int.cast_sum, sum_trace_Pp]
  norm_num

/-- **The proton spin up is one state.** -/
theorem rank_Pp : Pp.rank = 1 := by
  have h := rank_eq_trace Pp Pp_idem
  rw [trace_Pp] at h
  exact_mod_cast h

/-- **Unit charge:** `Tr P_{p↑}(I_z + 1/2) = 1`. -/
theorem charge_Pp : (Pp * (Izf + (1 / 2 : ℚ) • 1)).trace = 1 := by
  rw [Izf_half, Pp_eq, Matrix.smul_mul, mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_smul, trace_Psym_kron, smul_eq_mul]
  have e : ∀ π : Equiv.Perm (Fin 3), (R π * (C3 * Dq)).trace * (R π * (Dq * Dq)).trace =
      (1 / 8 : ℚ) * (((permZ π * (c3Z * d2Z)).trace * (permZ π * (d2Z * d2Z)).trace : ℤ) : ℚ) := by
    intro π
    have hDD : Dq * Dq = (1 / 4 : ℚ) • toQ (d2Z * d2Z) := by
      rw [Dq_eq, smul_mul_smul_comm, map_mul]
      norm_num
    rw [C3, trace_Dq_mul, hDD, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_R_mul]
    push_cast
    ring
  simp only [e, ← Finset.mul_sum]
  rw [← Int.cast_sum, sum_trace_charge]
  norm_num

/-- **The axial current of the projected proton:**
`Tr P_{p↑} Σ_r σ_z^{(r)} τ_z^{(r)} = ⟨p↑|Σ_r σ_zτ_z|p↑⟩ = 5/3`. -/
theorem axial_Pp : (Pp * axial).trace = 5 / 3 := by
  rw [Pp_eq, axial, Matrix.smul_mul, Finset.mul_sum, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul]
  have e : ∀ r : Fin 3, (Psym * ((C3 * Dq) ⊗ₖ Dq) * (sz r ⊗ₖ sz r)).trace =
      (1 / 24 : ℚ) * ((∑ π : Equiv.Perm (Fin 3),
        (permZ π * (c3Z * d2Z * szZ r)).trace * (permZ π * (d2Z * szZ r)).trace : ℤ) : ℚ) := by
    intro r
    rw [mul_assoc, ← Matrix.mul_kronecker_mul, trace_Psym_kron]
    have e2 : ∀ π : Equiv.Perm (Fin 3), (R π * (C3 * Dq * sz r)).trace * (R π * (Dq * sz r)).trace =
        (1 / 4 : ℚ) * (((permZ π * (c3Z * d2Z * szZ r)).trace *
          (permZ π * (d2Z * szZ r)).trace : ℤ) : ℚ) := by
      intro π
      have h1 : C3 * Dq * sz r = (1 / 2 : ℚ) • toQ (c3Z * d2Z * szZ r) := by
        rw [Dq_eq, C3, sz, Matrix.mul_smul, Matrix.smul_mul, map_mul, map_mul]
      have h2 : Dq * sz r = (1 / 2 : ℚ) • toQ (d2Z * szZ r) := by
        rw [Dq_eq, sz, Matrix.smul_mul, map_mul]
      rw [h1, h2, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
        smul_eq_mul, smul_eq_mul, trace_R_mul, trace_R_mul]
      push_cast
      ring
    simp only [e2, ← Finset.mul_sum]
    rw [← Int.cast_sum]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [← Int.cast_sum, sum_trace_axial]
  norm_num

end Comparison.Formulas.Nucleon
