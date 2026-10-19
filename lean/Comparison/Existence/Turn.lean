module

public import Comparison.Existence.Covariance
public import Comparison.Existence.Gauge

/-!
# Book VII. The parallel rotation is the rotation of the six on every division (Proposition 36)

* `degreeProj k`: `Π_k`, the projector onto the sets with `k` directions.
  `Tx_eq_sum_degrees`: **`T_ab = Σ_k Π_k J_a J_b Π_k`** for `a ≠ b`: the rotation is the part of two
  vertical steps that keeps the number of divided directions.
* `Tx_cube`: `T_ab³ = −T_ab` (`a ≠ b`); `exp_smul_of_cube`: in any complete normed real algebra,
  `T³ = −T` gives `e^{ϑT} = 1 + sin ϑ T + (1 − cos ϑ)T²`.
* `turnGen a b = E_ab − E_ba` (Gauge's `unitTurn`); `planeRot a b ϑ = 1 + sin ϑ X + (1 − cos ϑ)X²`,
  `exp_unitTurn`: `e^{ϑ(E_ab − E_ba)} = planeRot a b ϑ`, the rotation of the plane `(a, b)` by `ϑ`
  (`planeRot_col_a`, `planeRot_col_b`, `planeRot_col_other`).
* `extMap_planeRot`: `Λ(planeRot a b ϑ) = 1 + sin ϑ T_ab + (1 − cos ϑ)T_ab²`.
* `exp_parallel_turn`: **`e^{ϑ T_ab} = Λ(e^{ϑ(E_ab − E_ba)})`**, as `64 × 64` matrices for the six
  (any number of directions).
-/

@[expose] public section

namespace Comparison

open Finset
open scoped Matrix

/-! ## The degrees of the sixty-four sets -/

section Degrees

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **`Π_k`**, the projector onto the sets with `k` directions. -/
def degreeProj (k : ℕ) : Module.End R (Finset (Fin n) → R) where
  toFun v T := if T.card = k then v T else 0
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem degreeProj_apply (k : ℕ) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    degreeProj k v T = if T.card = k then v T else 0 := rfl

/-- Two directions more change the degree. -/
theorem εε_degree (a b : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    (εx a * εx b : Module.End R (Finset (Fin n) → R)) (degreeProj T.card v) T = 0 := by
  simp only [Module.End.mul_apply, εx_apply, degreeProj_apply]
  by_cases ha : a ∈ T
  · by_cases hb : b ∈ T.erase a
    · have h1 := Finset.card_erase_of_mem hb
      have h2 := Finset.card_erase_of_mem ha
      have h3 : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
      have h4 : 1 ≤ (T.erase a).card := Finset.card_pos.mpr ⟨b, hb⟩
      have hne : ((T.erase a).erase b).card ≠ T.card := by omega
      rw [ite_eq_left ha, ite_eq_left hb, ite_eq_right hne, mul_zero, mul_zero]
    · rw [ite_eq_left ha, ite_eq_right hb, mul_zero]
  · rw [ite_eq_right ha]

/-- Two directions fewer change the degree. -/
theorem ιι_degree (a b : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    (ιx a * ιx b : Module.End R (Finset (Fin n) → R)) (degreeProj T.card v) T = 0 := by
  simp only [Module.End.mul_apply, ιx_apply, degreeProj_apply]
  by_cases ha : a ∈ T
  · rw [ite_eq_left ha]
  · by_cases hb : b ∈ insert a T
    · rw [ite_eq_right ha, ite_eq_left hb, mul_zero]
    · have h1 := Finset.card_insert_of_notMem hb
      have h2 := Finset.card_insert_of_notMem ha
      have hne : (insert b (insert a T)).card ≠ T.card := by omega
      rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right hne, mul_zero, mul_zero]

/-- The rotation keeps the degree. -/
theorem Tx_degree (a b : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    Tx a b (degreeProj T.card v) T = Tx a b v T := by
  have key : ∀ x y : Fin n, (εx x * ιx y : Module.End R (Finset (Fin n) → R)) (degreeProj T.card v) T =
      (εx x * ιx y : Module.End R (Finset (Fin n) → R)) v T := by
    intro x y
    simp only [Module.End.mul_apply, εx_apply, ιx_apply, degreeProj_apply]
    by_cases hx : x ∈ T
    · by_cases hy : y ∈ T.erase x
      · simp [hx, hy]
      · have h1 := Finset.card_insert_of_notMem hy
        have h2 := Finset.card_erase_of_mem hx
        have h3 : 1 ≤ T.card := Finset.card_pos.mpr ⟨x, hx⟩
        have heq : (insert y (T.erase x)).card = T.card := by omega
        simp [hx, hy, heq]
    · simp [hx]
  simp only [Tx, LinearMap.sub_apply, Pi.sub_apply]
  rw [key, key]

/-- **Proposition 36:** `T_ab = Σ_k Π_k J_a J_b Π_k` for `a ≠ b`. -/
theorem Tx_eq_sum_degrees {a b : Fin n} (hab : a ≠ b) :
    Tx (R := R) a b = ∑ k ∈ Finset.range (n + 1), degreeProj k * (Jx a * Jx b) * degreeProj k := by
  refine LinearMap.ext fun v => funext fun T => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [Module.End.mul_apply, degreeProj_apply]
  have hT : T.card ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    have := Finset.card_le_univ T
    rw [Fintype.card_fin] at this
    omega
  rw [Finset.sum_ite_eq, ite_eq_left hT, ← Module.End.mul_apply (Jx a) (Jx b), Jx_mul_Jx hab,
    LinearMap.add_apply, LinearMap.add_apply, Pi.add_apply, Pi.add_apply, εε_degree, ιι_degree,
    Tx_degree, add_zero, add_zero]

end Degrees

/-! ## The rotation of a plane on the sets -/

section TurnSets

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **One direction fewer on a basis set:** `ι_a f_S = (−1)^{#{c ∈ S : c < a}} f_{S ∖ {a}}` for
`a ∈ S`, zero otherwise. -/
theorem ιx_single (a : Fin n) (S : Finset (Fin n)) :
    ιx (R := R) a (Pi.single S 1) =
      if a ∈ S then extSign (R := R) a (S.erase a) • (Pi.single (S.erase a) 1 : Finset (Fin n) → R)
      else 0 := by
  funext T
  simp only [ιx_apply, Pi.single_apply]
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hT : T = S.erase a
    · subst hT
      simp [Finset.insert_erase ha]
    · by_cases haT : a ∈ T
      · simp [haT, hT]
      · have : insert a T ≠ S := fun h => hT (by rw [← h, Finset.erase_insert haT])
        simp [haT, hT, this]
  · simp only [ha, ↓reduceIte, Pi.zero_apply]
    by_cases haT : a ∈ T
    · simp [haT]
    · have : insert a T ≠ S := fun h => ha (h ▸ Finset.mem_insert_self a T)
      simp [haT, this]

/-- The rotation of `(a, b)` kills a set holding neither `a` nor `b`. -/
theorem Tx_single_singlet {a b : Fin n} {S : Finset (Fin n)} (ha : a ∉ S) (hb : b ∉ S) :
    Tx (R := R) a b (Pi.single S 1) = 0 := by
  simp [Tx, LinearMap.sub_apply, Module.End.mul_apply, ιx_single, ha, hb]

/-- The rotation of `(a, b)` kills a set holding both. -/
theorem Tx_single_both {a b : Fin n} (hab : a ≠ b) {S : Finset (Fin n)} (ha : a ∈ S)
    (hb : b ∈ S) : Tx (R := R) a b (Pi.single S 1) = 0 := by
  have ha' : a ∈ S.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  simp [Tx, LinearMap.sub_apply, Module.End.mul_apply, ιx_single, ha, hb, εx_single, ha', hb']

theorem Tx_εx_self_left {a b : Fin n} (hab : a ≠ b) :
    Tx (R := R) a b * εx a = εx a * Tx a b - εx b := by
  have h := Tx_εx (R := R) a b a
  rw [ite_eq_right (Ne.symm hab), ite_eq_left rfl, zero_sub] at h
  calc Tx a b * εx a = (Tx a b * εx a - εx a * Tx a b) + εx a * Tx a b := by abel
    _ = εx a * Tx a b - εx b := by rw [h]; abel

theorem Tx_εx_self_right {a b : Fin n} (hab : a ≠ b) :
    Tx (R := R) a b * εx b = εx b * Tx a b + εx a := by
  have h := Tx_εx (R := R) a b b
  rw [ite_eq_left rfl, ite_eq_right hab, sub_zero] at h
  calc Tx a b * εx b = (Tx a b * εx b - εx b * Tx a b) + εx b * Tx a b := by abel
    _ = εx b * Tx a b + εx a := by rw [h]; abel

/-- On a set holding neither, `T ε_a f = −ε_b f` and `T ε_b f = ε_a f`. -/
theorem Tx_εa_singlet {a b : Fin n} (hab : a ≠ b) {S : Finset (Fin n)} (ha : a ∉ S) (hb : b ∉ S) :
    Tx (R := R) a b (εx a (Pi.single S 1)) = -εx b (Pi.single S 1) := by
  rw [← Module.End.mul_apply (Tx a b) (εx a), Tx_εx_self_left hab, LinearMap.sub_apply,
    Module.End.mul_apply, Tx_single_singlet ha hb, map_zero, zero_sub]

theorem Tx_εb_singlet {a b : Fin n} (hab : a ≠ b) {S : Finset (Fin n)} (ha : a ∉ S) (hb : b ∉ S) :
    Tx (R := R) a b (εx b (Pi.single S 1)) = εx a (Pi.single S 1) := by
  rw [← Module.End.mul_apply (Tx a b) (εx b), Tx_εx_self_right hab, LinearMap.add_apply,
    Module.End.mul_apply, Tx_single_singlet ha hb, map_zero, zero_add]

/-- A set holding `a` is `± ε_a` of the set without it. -/
theorem single_eq_εx {a : Fin n} {S : Finset (Fin n)} (ha : a ∈ S) :
    (Pi.single S 1 : Finset (Fin n) → R) =
      extSign (R := R) a (S.erase a) • εx a (Pi.single (S.erase a) 1) := by
  rw [εx_single, ite_eq_right (Finset.notMem_erase a S), smul_smul, extSign_mul_self, one_smul,
    Finset.insert_erase ha]

/-- **`T_ab³ = −T_ab`** for `a ≠ b`. -/
theorem Tx_cube {a b : Fin n} (hab : a ≠ b) : Tx (R := R) a b * Tx a b * Tx a b = -Tx a b := by
  refine endo_ext fun S => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · rw [Tx_single_both hab ha hb]
    simp
  · have ha0 : a ∉ S.erase a := Finset.notMem_erase a S
    have hb0 : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    rw [single_eq_εx ha]
    simp only [map_smul, Tx_εa_singlet hab ha0 hb0, map_neg, Tx_εb_singlet hab ha0 hb0, smul_neg,
      neg_neg]
  · have ha0 : a ∉ S.erase b := fun h => ha (Finset.mem_of_mem_erase h)
    have hb0 : b ∉ S.erase b := Finset.notMem_erase b S
    rw [single_eq_εx hb]
    simp only [map_smul, Tx_εb_singlet hab ha0 hb0, Tx_εa_singlet hab ha0 hb0, map_neg, smul_neg,
      neg_neg]
  · rw [Tx_single_singlet ha hb]
    simp

end TurnSets

/-! ## The exponential of a rotation of square minus a projector -/

section Exp

/-- **In a complete normed real algebra, `T³ = −T` gives `e^{ϑT} = 1 + sin ϑ T + (1 − cos ϑ)T²`.** -/
theorem exp_smul_of_cube {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (T : 𝔸) (hT : T * T * T = -T) (θ : ℝ) :
    NormedSpace.exp (θ • T) = 1 + Real.sin θ • T + (1 - Real.cos θ) • (T * T) := by
  have hodd : ∀ k : ℕ, T ^ (2 * k + 1) = ((-1 : ℝ) ^ k) • T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ih, pow_two, smul_mul_assoc,
        ← mul_assoc, hT, pow_succ, mul_neg_one, neg_smul, smul_neg]
  have heven : ∀ k : ℕ, T ^ (2 * k + 2) = ((-1 : ℝ) ^ k) • (T * T) := by
    intro k
    induction k with
    | zero => simp [pow_two]
    | succ k ih =>
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, pow_add, ih, pow_two, smul_mul_assoc,
        ← mul_assoc, hT, pow_succ, mul_neg_one, neg_smul, neg_mul, smul_neg]
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  set f : ℕ → 𝔸 := fun n => ((n.factorial : ℝ)⁻¹) • (θ • T) ^ n with hf
  have hc := ((Real.hasSum_cos θ).smul_const (-(T * T))).add (hasSum_ite_eq 0 (1 + T * T))
  have hs := (Real.hasSum_sin θ).smul_const T
  have he : HasSum (fun k => f (2 * k)) (Real.cos θ • -(T * T) + (1 + T * T)) := by
    convert hc using 1
    funext k
    rcases k with _ | k
    · simp only [hf, Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        mul_one, div_one, ↓reduceIte]
      module
    · simp only [hf]
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, smul_pow, heven k, smul_smul, smul_smul]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [pow_succ (-1 : ℝ) k]
      module
  have ho : HasSum (fun k => f (2 * k + 1)) (Real.sin θ • T) := by
    convert hs using 1
    funext k
    simp only [hf]
    rw [smul_pow, hodd k, smul_smul, smul_smul]
    congr 1
    ring
  convert he.even_add_odd ho using 1
  module

end Exp

/-! ## The rotation of a plane of the six -/

section Rotation

variable {n : ℕ}

/-- `E_ab − E_ba` with `Matrix.single`. -/
def turnGen (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single a b 1 - Matrix.single b a 1

theorem turnGen_eq_unitTurn (a b : Fin n) : turnGen a b = unitTurn a b := by
  ext i j
  have e1 : (a = i ∧ b = j) ↔ (i = a ∧ j = b) :=
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have e2 : (b = i ∧ a = j) ↔ (i = b ∧ j = a) :=
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  simp only [turnGen, unitTurn, Matrix.sub_apply, Matrix.single_apply, Matrix.of_apply, e1, e2]

theorem turnGen_sq {a b : Fin n} (hab : a ≠ b) :
    turnGen a b * turnGen a b = -(Matrix.single a a 1 + Matrix.single b b 1) := by
  rw [turnGen, sub_mul, mul_sub, mul_sub, Matrix.single_mul_single_of_ne (h := Ne.symm hab),
    Matrix.single_mul_single_same, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne (h := hab)]
  simp only [mul_one]
  abel

theorem turnGen_cube {a b : Fin n} (hab : a ≠ b) :
    turnGen a b * turnGen a b * turnGen a b = -turnGen a b := by
  rw [turnGen_sq hab, turnGen, neg_mul, add_mul, mul_sub, mul_sub, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne (h := hab), Matrix.single_mul_single_of_ne (h := Ne.symm hab),
    Matrix.single_mul_single_same]
  simp only [mul_one]
  abel

/-- **The rotation of the plane `(a, b)` by `ϑ`:** `1 + sin ϑ X + (1 − cos ϑ)X²`,
`X = E_ab − E_ba`. -/
noncomputable def planeRot (a b : Fin n) (θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + Real.sin θ • turnGen a b + (1 - Real.cos θ) • (turnGen a b * turnGen a b)

theorem planeRot_apply {a b : Fin n} (hab : a ≠ b) (θ : ℝ) (i j : Fin n) :
    planeRot a b θ i j =
      (if i = j then 1 else 0) + Real.sin θ * ((if a = i ∧ b = j then 1 else 0) -
        (if b = i ∧ a = j then 1 else 0)) -
        (1 - Real.cos θ) *
          ((if a = i ∧ a = j then 1 else 0) + (if b = i ∧ b = j then 1 else 0)) := by
  rw [planeRot, turnGen_sq hab]
  simp only [turnGen, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.one_apply, Matrix.single_apply, smul_eq_mul]
  ring

theorem planeRot_col_a {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    (planeRot a b θ).col a = Real.cos θ • Pi.single a 1 - Real.sin θ • Pi.single b 1 := by
  funext i
  rw [Matrix.col_apply, planeRot_apply hab]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hia : i = a
  · rw [hia]
    simp [hab, Ne.symm hab]
  · by_cases hib : i = b
    · rw [hib]
      simp [hab, Ne.symm hab]
    · simp [hia, hib, Ne.symm hia, Ne.symm hib]

theorem planeRot_col_b {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    (planeRot a b θ).col b = Real.sin θ • Pi.single a 1 + Real.cos θ • Pi.single b 1 := by
  funext i
  rw [Matrix.col_apply, planeRot_apply hab]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hia : i = a
  · rw [hia]
    simp [hab, Ne.symm hab]
  · by_cases hib : i = b
    · rw [hib]
      simp [hab, Ne.symm hab]
    · simp [hia, hib, Ne.symm hia, Ne.symm hib]

theorem planeRot_col_other {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (θ : ℝ) :
    (planeRot a b θ).col c = Pi.single c 1 := by
  funext i
  rw [Matrix.col_apply, planeRot_apply hab]
  simp only [Pi.single_apply]
  simp [hca, hcb, Ne.symm hca, Ne.symm hcb]

theorem εv_sub {R : Type*} [CommRing R] (v w : Fin n → R) : εv (v - w) = εv v - εv w := by
  have h := εv_add (v - w) w
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem colStep_rot_a {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    colStep (planeRot a b θ) a = Real.cos θ • εx a - Real.sin θ • εx b := by
  rw [colStep, planeRot_col_a hab, εv_sub, εv_smul, εv_smul, εv_single, εv_single]

theorem colStep_rot_b {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    colStep (planeRot a b θ) b = Real.sin θ • εx a + Real.cos θ • εx b := by
  rw [colStep, planeRot_col_b hab, εv_add, εv_smul, εv_smul, εv_single, εv_single]

theorem colStep_rot_other {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (θ : ℝ) :
    colStep (planeRot a b θ) c = εx c := by
  rw [colStep, planeRot_col_other hab hca hcb, εv_single]

/-- The rotation fixes a set holding neither `a` nor `b`. -/
theorem extMap_rot_singlet {a b : Fin n} (hab : a ≠ b) (θ : ℝ) {S : Finset (Fin n)} (ha : a ∉ S)
    (hb : b ∉ S) : extMap (planeRot a b θ) (Pi.single S 1) = Pi.single S 1 := by
  rw [extMap_single]
  have : ordProd (colStep (planeRot a b θ)) S = ordProd εx S := by
    refine ordProd_congr fun c hc => ?_
    exact colStep_rot_other hab (fun h => ha (h ▸ hc)) (fun h => hb (h ▸ hc)) θ
  rw [this, ordProd_εx_vac]

/-- `Λ(R) ε_c f = ε(Re_c) f` on a set held fixed by `R`. -/
theorem extMap_rot_εx {a b : Fin n} (hab : a ≠ b) (θ : ℝ) {S : Finset (Fin n)} (ha : a ∉ S)
    (hb : b ∉ S) (c : Fin n) :
    extMap (planeRot a b θ) (εx c (Pi.single S 1)) = colStep (planeRot a b θ) c (Pi.single S 1) := by
  rw [← Module.End.mul_apply (extMap _) (εx c), extMap_εx, Module.End.mul_apply,
    extMap_rot_singlet hab θ ha hb]

/-- **`Λ(planeRot a b ϑ) = 1 + sin ϑ T_ab + (1 − cos ϑ)T_ab²`.** -/
theorem extMap_planeRot {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    extMap (planeRot a b θ) =
      1 + Real.sin θ • Tx a b + (1 - Real.cos θ) • (Tx (R := ℝ) a b * Tx a b) := by
  refine endo_ext fun S => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · -- both
    have hb1 : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    have ha0 : a ∉ (S.erase a).erase b :=
      fun h => Finset.notMem_erase a S (Finset.mem_of_mem_erase h)
    have hb0 : b ∉ (S.erase a).erase b := Finset.notMem_erase b (S.erase a)
    have hS : (Pi.single S 1 : Finset (Fin n) → ℝ) =
        (extSign (R := ℝ) a (S.erase a) * extSign (R := ℝ) b ((S.erase a).erase b)) •
          εx a (εx b (Pi.single ((S.erase a).erase b) 1)) := by
      rw [single_eq_εx ha, single_eq_εx hb1, map_smul, smul_smul]
    rw [Tx_single_both hab ha hb]
    simp only [map_zero, smul_zero, add_zero]
    rw [hS, map_smul, ← Module.End.mul_apply (extMap _) (εx a), extMap_εx, Module.End.mul_apply,
      extMap_rot_εx hab θ ha0 hb0, colStep_rot_a hab, colStep_rot_b hab]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_sub,
      map_smul]
    have h1 : εx (R := ℝ) a (εx a (Pi.single ((S.erase a).erase b) 1)) = 0 := by
      rw [← Module.End.mul_apply, εx_mul_self, LinearMap.zero_apply]
    have h2 : εx (R := ℝ) b (εx b (Pi.single ((S.erase a).erase b) 1)) = 0 := by
      rw [← Module.End.mul_apply, εx_mul_self, LinearMap.zero_apply]
    have h3 : εx (R := ℝ) b (εx a (Pi.single ((S.erase a).erase b) 1)) =
        -εx a (εx b (Pi.single ((S.erase a).erase b) 1)) := by
      rw [← Module.End.mul_apply, εx_εx_ne a b, LinearMap.neg_apply, Module.End.mul_apply]
    rw [h1, h2, h3]
    have hcs := Real.cos_sq_add_sin_sq θ
    calc _ = ((extSign (R := ℝ) a (S.erase a) * extSign (R := ℝ) b ((S.erase a).erase b)) *
          (Real.cos θ ^ 2 + Real.sin θ ^ 2)) •
          εx (R := ℝ) a (εx b (Pi.single ((S.erase a).erase b) 1)) := by module
      _ = _ := by rw [hcs, mul_one]
  · -- `a` only
    have ha0 : a ∉ S.erase a := Finset.notMem_erase a S
    have hb0 : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    rw [single_eq_εx ha]
    simp only [map_smul, Tx_εa_singlet hab ha0 hb0, map_neg, Tx_εb_singlet hab ha0 hb0]
    rw [extMap_rot_εx hab θ ha0 hb0, colStep_rot_a hab, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply]
    module
  · -- `b` only
    have ha0 : a ∉ S.erase b := fun h => ha (Finset.mem_of_mem_erase h)
    have hb0 : b ∉ S.erase b := Finset.notMem_erase b S
    rw [single_eq_εx hb]
    simp only [map_smul, Tx_εb_singlet hab ha0 hb0, Tx_εa_singlet hab ha0 hb0, map_neg]
    rw [extMap_rot_εx hab θ ha0 hb0, colStep_rot_b hab, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply]
    module
  · -- neither
    rw [Tx_single_singlet ha hb, extMap_rot_singlet hab θ ha hb]
    simp


end Rotation

/-! ## Proposition 36: `e^{ϑ T_ab} = Λ(e^{ϑ(E_ab − E_ba)})` -/

section ExpTurn

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- `e^{ϑM} = 1 + sin ϑ M + (1 − cos ϑ)M²` for a real matrix with `M³ = −M`. -/
theorem matrix_exp_smul_of_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M * M * M = -M) (θ : ℝ) :
    NormedSpace.exp (θ • M) = 1 + Real.sin θ • M + (1 - Real.cos θ) • (M * M) :=
  open scoped Matrix.Norms.Operator in exp_smul_of_cube M hM θ

/-- **`e^{ϑ(E_ab − E_ba)}` is the rotation of the plane `(a, b)` by `ϑ`.** -/
theorem exp_unitTurn {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    NormedSpace.exp (θ • unitTurn a b) = planeRot a b θ := by
  rw [← turnGen_eq_unitTurn, matrix_exp_smul_of_cube _ (turnGen_cube hab), planeRot]

/-- **Proposition 36:** `e^{ϑ T_ab} = Λ(e^{ϑ(E_ab − E_ba)})` for `a ≠ b`, as matrices on the sets. -/
theorem exp_parallel_turn {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    NormedSpace.exp (θ • LinearMap.toMatrixAlgEquiv' (Tx (R := ℝ) a b)) =
      LinearMap.toMatrixAlgEquiv' (extMap (NormedSpace.exp (θ • unitTurn a b))) := by
  have hcube : LinearMap.toMatrixAlgEquiv' (Tx (R := ℝ) a b) *
      LinearMap.toMatrixAlgEquiv' (Tx (R := ℝ) a b) * LinearMap.toMatrixAlgEquiv' (Tx (R := ℝ) a b) =
      -LinearMap.toMatrixAlgEquiv' (Tx (R := ℝ) a b) := by
    rw [← map_mul, ← map_mul, Tx_cube hab, map_neg]
  rw [matrix_exp_smul_of_cube _ hcube, exp_unitTurn hab, extMap_planeRot hab, map_add, map_add,
    map_smul, map_smul, map_one, map_mul]

end ExpTurn

end Comparison

end
