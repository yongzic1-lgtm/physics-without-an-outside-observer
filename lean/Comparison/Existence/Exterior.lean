module

public import Mathlib

/-!
# Book VII. The vertical completion on the exterior algebra of the six

The exterior algebra of `n` directions has
the basis `f_S`, `S ⊆ {0, …, n−1}`; a vector is its coefficient function `Finset (Fin n) → R`. For
`n = 6` it is the 64-dimensional exterior algebra of the six (`finrank_ext_six`).

* `εx a`: one direction more, `f_S ↦ ± f_{S ∪ {a}}` (zero when `a ∈ S`); `ιx a`: one direction
  fewer, `f_S ↦ ± f_{S ∖ {a}}`; the sign is `(−1)^{#{c ∈ S : c < a}}` (`extSign`).
* `εx_ιx_add`: `ε_a ι_b + ι_b ε_a = δ_ab`; `εx_εx_add`, `ιx_ιx_add`: `ε_a ε_b + ε_b ε_a = 0`,
  `ι_a ι_b + ι_b ι_a = 0`; `ιx_adjoint`: `ι_a` is the transpose of `ε_a`.
* `Jx a = ε_a + ι_a` (the vertical step): `Jx_mul_self`: `J_a² = 1`; `Jx_anticomm`:
  `J_a J_b = −J_b J_a` for `a ≠ b`; `shortest_loop`: `J_a J_b J_a J_b = −1`.
* `Tx a b = ε_a ι_b − ε_b ι_a` (the parallel rotation): `Jx_mul_Jx`: `J_a J_b = T_ab + ε_a ε_b + ι_a ι_b`
  for `a ≠ b`; `Jx_mul_Jx'`: with `T'_ab = ε_a ι_b + ι_a ε_b` it holds for all `a, b`, and
  `T'_ab = T_ab` for `a ≠ b`, `T'_aa = 1`.
* `Nx`, the number of directions: `Nx_eq_sum`: `N = Σ_a ε_a ι_a`; `Nx_εx`, `Nx_ιx`: `ε` raises it by
  one and `ι` lowers it by one; `Nx_Tx`: `T_ab` keeps it.
* `Tx_εx`, `Tx_ιx`, `Tx_Jx`: `[T_ab, ε_c] = δ_bc ε_a − δ_ac ε_b`, the same for `ι` and `J`: `T_ab`
  turns the plane `(a, b)`.
* `volume_sq`: on the six, `w = J₀J₁J₂J₃J₄J₅` has `w² = −1`; `half_anticomm`, `half_prod`: with the
  square root of the sign `f_x = i^{[x ∈ D]} J_x`, `f_x f_y + f_y f_x = 2 θ_D(x) δ_xy` and `f₀ ⋯ f₅ = i^{|D|} w`.
-/

@[expose] public section

namespace Comparison

open Finset

/-! ## Signs -/

section General

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The sign of putting the direction `a` in front of the set `S`: `(−1)^{#{c ∈ S : c < a}}`. -/
def extSign (a : Fin n) (S : Finset (Fin n)) : R := (-1) ^ (S.filter (· < a)).card

theorem extSign_mul_self (a : Fin n) (S : Finset (Fin n)) :
    extSign (R := R) a S * extSign a S = 1 := by
  rw [extSign, ← pow_add, ← two_mul, pow_mul]
  simp

theorem extSign_insert {a b : Fin n} {S : Finset (Fin n)} (hb : b ∉ S) :
    extSign (R := R) a (insert b S) = (if b < a then -1 else 1) * extSign a S := by
  unfold extSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hb (Finset.mem_filter.mp h').1), pow_succ]
    ring
  · rw [one_mul]

/-- Exactly one of `a < b`, `b < a` holds for `a ≠ b`. -/
theorem sign_pair {a b : Fin n} (hab : a ≠ b) :
    ((if a < b then -1 else 1) * (if b < a then -1 else 1) : R) = -1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h]

theorem sign_pair_add {a b : Fin n} (hab : a ≠ b) :
    ((if a < b then -1 else 1) + (if b < a then -1 else 1) : R) = 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h]

/-! ## One direction more, one direction fewer -/

/-- **One direction more:** `ε_a f_S = (−1)^{#{c ∈ S : c < a}} f_{S ∪ {a}}` for `a ∉ S`, and
`ε_a f_S = 0` for `a ∈ S`. On coefficient functions: `(ε_a v)(T) = ± v(T ∖ {a})` for `a ∈ T`. -/
def εx (a : Fin n) : Module.End R (Finset (Fin n) → R) where
  toFun v T := if a ∈ T then extSign a (T.erase a) * v (T.erase a) else 0
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **One direction fewer:** `ι_a f_S = (−1)^{#{c ∈ S : c < a}} f_{S ∖ {a}}` for `a ∈ S`, zero
otherwise. On coefficient functions: `(ι_a v)(T) = ± v(T ∪ {a})` for `a ∉ T`. -/
def ιx (a : Fin n) : Module.End R (Finset (Fin n) → R) where
  toFun v T := if a ∈ T then 0 else extSign a T * v (insert a T)
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem εx_apply (a : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    εx a v T = if a ∈ T then extSign a (T.erase a) * v (T.erase a) else 0 := rfl

theorem ιx_apply (a : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    ιx a v T = if a ∈ T then 0 else extSign a T * v (insert a T) := rfl

/-- `ι_a` is the transpose of `ε_a`: `Σ_T w(T) (ε_a v)(T) = Σ_S (ι_a w)(S) v(S)`. -/
theorem ιx_adjoint (a : Fin n) (v w : Finset (Fin n) → R) :
    ∑ T, w T * εx a v T = ∑ S, ιx a w S * v S := by
  have hL : ∑ T, w T * εx a v T = ∑ T ∈ Finset.univ.filter (fun T => a ∈ T),
      w T * (extSign a (T.erase a) * v (T.erase a)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [εx_apply]
    split_ifs <;> simp
  have hR : ∑ S, ιx a w S * v S = ∑ S ∈ Finset.univ.filter (fun S => a ∉ S),
      extSign a S * w (insert a S) * v S := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [ιx_apply]
    split_ifs <;> simp
  rw [hL, hR]
  refine Finset.sum_nbij' (fun T => T.erase a) (fun S => insert a S) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact Finset.notMem_erase a T
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_insert_self a S
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact Finset.insert_erase hT
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.erase_insert hS
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    rw [Finset.insert_erase hT]
    ring

/-! ## The canonical anticommutation relations -/

theorem εx_mul_self (a : Fin n) : εx (R := R) a * εx a = 0 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, εx_apply, LinearMap.zero_apply, Pi.zero_apply,
    Finset.notMem_erase, ↓reduceIte, mul_zero, ite_self]

theorem ιx_mul_self (a : Fin n) : ιx (R := R) a * ιx a = 0 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, ιx_apply, LinearMap.zero_apply, Pi.zero_apply,
    Finset.mem_insert_self, ↓reduceIte, mul_zero, ite_self]

/-- `ε_a ι_a + ι_a ε_a = 1`. -/
theorem εx_ιx_self (a : Fin n) : εx (R := R) a * ιx a + ιx a * εx a = 1 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, Pi.add_apply,
    εx_apply, ιx_apply]
  by_cases ha : a ∈ T
  · simp only [ha, Finset.notMem_erase, ↓reduceIte, Finset.insert_erase ha, add_zero]
    rw [← mul_assoc, extSign_mul_self, one_mul]
  · simp only [ha, Finset.mem_insert_self, ↓reduceIte, Finset.erase_insert ha, zero_add]
    rw [← mul_assoc, extSign_mul_self, one_mul]

/-- `ε_a ι_b + ι_b ε_a = 0` for `a ≠ b`. -/
theorem εx_ιx_ne {a b : Fin n} (hab : a ≠ b) : εx (R := R) a * ιx b + ιx b * εx a = 0 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
    Pi.zero_apply, εx_apply, ιx_apply]
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
  · have hb' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    simp [ha, hb, hb']
  · have hb' : b ∉ T.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    have ha' : a ∈ insert b T := Finset.mem_insert_of_mem ha
    simp only [ha, hb, hb', ha', ↓reduceIte]
    rw [Finset.erase_insert_of_ne (Ne.symm hab)]
    have e1 : extSign (R := R) a (insert b (T.erase a)) =
        (if b < a then -1 else 1) * extSign a (T.erase a) := extSign_insert hb'
    have e2 : extSign (R := R) b T = (if a < b then -1 else 1) * extSign b (T.erase a) := by
      conv_lhs => rw [← Finset.insert_erase ha]
      exact extSign_insert (Finset.notMem_erase a T)
    rw [e1, e2]
    have hp := sign_pair (R := R) hab
    linear_combination (extSign a (T.erase a) * extSign b (T.erase a) *
      v (insert b (T.erase a))) * hp
  · simp [ha, hb]
  · have ha' : a ∉ insert b T := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hab, ha⟩
    simp [ha, hb, ha']

/-- **The anticommutation of one more and one fewer:** `ε_a ι_b + ι_b ε_a = δ_ab`. -/
theorem εx_ιx_add (a b : Fin n) :
    εx (R := R) a * ιx b + ιx b * εx a = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h
    exact εx_ιx_self a
  · exact εx_ιx_ne h

/-- `ε_a ε_b + ε_b ε_a = 0`. -/
theorem εx_εx_add (a b : Fin n) : εx (R := R) a * εx b + εx b * εx a = 0 := by
  by_cases hab : a = b
  · subst hab
    rw [εx_mul_self, add_zero]
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
    Pi.zero_apply, εx_apply]
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
  · have hb' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    have ha' : a ∈ T.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    simp only [ha, hb, hb', ha', ↓reduceIte]
    rw [Finset.erase_right_comm (a := b) (b := a)]
    set U := (T.erase a).erase b with hU
    have hbU : b ∉ U := Finset.notMem_erase b _
    have haU : a ∉ U := fun h => Finset.notMem_erase a T (Finset.mem_of_mem_erase h)
    have e1 : extSign (R := R) a (T.erase a) = (if b < a then -1 else 1) * extSign a U := by
      conv_lhs => rw [← Finset.insert_erase hb']
      exact extSign_insert hbU
    have e2 : extSign (R := R) b (T.erase b) = (if a < b then -1 else 1) * extSign b U := by
      rw [show T.erase b = insert a U by
        rw [hU, Finset.erase_right_comm, Finset.insert_erase ha']]
      exact extSign_insert haU
    rw [e1, e2]
    have hp := sign_pair_add (R := R) hab
    linear_combination (extSign a U * extSign b U * v U) * hp
  · have hb' : b ∉ T.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    simp [ha, hb, hb']
  · have ha' : a ∉ T.erase b := fun h => ha (Finset.mem_of_mem_erase h)
    simp [ha, hb, ha']
  · simp [ha, hb]

/-- `ι_a ι_b + ι_b ι_a = 0`. -/
theorem ιx_ιx_add (a b : Fin n) : ιx (R := R) a * ιx b + ιx b * ιx a = 0 := by
  by_cases hab : a = b
  · subst hab
    rw [ιx_mul_self, add_zero]
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
    Pi.zero_apply, ιx_apply]
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
  · simp [ha, hb]
  · have ha' : a ∈ insert b T := Finset.mem_insert_of_mem ha
    simp [ha, hb, ha']
  · have hb' : b ∈ insert a T := Finset.mem_insert_of_mem hb
    simp [ha, hb, hb']
  · have hb' : b ∉ insert a T := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm hab, hb⟩
    have ha' : a ∉ insert b T := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hab, ha⟩
    simp only [ha, hb, ha', hb', ↓reduceIte]
    rw [Finset.insert_comm a b T]
    have e1 : extSign (R := R) b (insert a T) = (if a < b then -1 else 1) * extSign b T :=
      extSign_insert ha
    have e2 : extSign (R := R) a (insert b T) = (if b < a then -1 else 1) * extSign a T :=
      extSign_insert hb
    rw [e1, e2]
    have hp := sign_pair_add (R := R) hab
    linear_combination (extSign a T * extSign b T * v (insert b (insert a T))) * hp

/-! ## The vertical step `J_a = ε_a + ι_a` -/

/-- **The vertical step** along the direction `a`: one direction more plus one direction fewer. -/
def Jx (a : Fin n) : Module.End R (Finset (Fin n) → R) := εx a + ιx a

theorem ιx_εx_ne {a b : Fin n} (hab : a ≠ b) :
    ιx (R := R) b * εx a = -(εx a * ιx b) :=
  eq_neg_of_add_eq_zero_right (εx_ιx_ne hab)

theorem εx_εx_ne (a b : Fin n) : εx (R := R) b * εx a = -(εx a * εx b) :=
  eq_neg_of_add_eq_zero_right (εx_εx_add a b)

theorem ιx_ιx_ne (a b : Fin n) : ιx (R := R) b * ιx a = -(ιx a * ιx b) :=
  eq_neg_of_add_eq_zero_right (ιx_ιx_add a b)

/-- **`J_a² = 1`.** -/
theorem Jx_mul_self (a : Fin n) : Jx (R := R) a * Jx a = 1 := by
  rw [Jx, add_mul, mul_add, mul_add, εx_mul_self, ιx_mul_self, zero_add, add_zero,
    εx_ιx_self]

/-- **Two vertical steps along perpendicular directions anticommute.** -/
theorem Jx_anticomm {a b : Fin n} (hab : a ≠ b) :
    Jx (R := R) a * Jx b = -(Jx b * Jx a) := by
  simp only [Jx, add_mul, mul_add]
  rw [ιx_εx_ne hab, ιx_εx_ne (Ne.symm hab), εx_εx_ne a b, ιx_ιx_ne a b]
  abel

/-- `J_a J_b + J_b J_a = 2 δ_ab`. -/
theorem Jx_anticomm_add (a b : Fin n) :
    Jx (R := R) a * Jx b + Jx b * Jx a = if a = b then 2 else 0 := by
  split_ifs with h
  · subst h
    rw [Jx_mul_self, one_add_one_eq_two]
  · rw [Jx_anticomm h, neg_add_cancel]

/-- **The shortest vertical loop returns `−1`:** `J_a J_b J_a J_b = −1` for `a ≠ b`. -/
theorem shortest_loop {a b : Fin n} (hab : a ≠ b) :
    Jx (R := R) a * Jx b * Jx a * Jx b = -1 := by
  rw [Jx_anticomm hab, neg_mul, neg_mul, mul_assoc (Jx b), Jx_mul_self, mul_one, Jx_mul_self]

/-! ## The parallel rotation `T_ab` -/

/-- **The parallel rotation** of the plane `(a, b)`: `T_ab = ε_a ι_b − ε_b ι_a`. -/
def Tx (a b : Fin n) : Module.End R (Finset (Fin n) → R) := εx a * ιx b - εx b * ιx a

/-- **The two directions joined:** `J_a J_b = T_ab + ε_a ε_b + ι_a ι_b` for `a ≠ b`. -/
theorem Jx_mul_Jx {a b : Fin n} (hab : a ≠ b) :
    Jx (R := R) a * Jx b = Tx a b + εx a * εx b + ιx a * ιx b := by
  simp only [Jx, Tx, add_mul, mul_add]
  rw [ιx_εx_ne (Ne.symm hab)]
  abel

/-- At `a = b` the left side is `1` and the right side is `0`: the hypothesis `a ≠ b` is needed. -/
theorem Jx_mul_Jx_diag (a : Fin n) :
    Jx (R := R) a * Jx a = 1 ∧ Tx (R := R) a a + εx a * εx a + ιx a * ιx a = 0 := by
  refine ⟨Jx_mul_self a, ?_⟩
  rw [Tx, sub_self, εx_mul_self, ιx_mul_self, add_zero, add_zero]

/-- The rotation written for all `a, b`: `T'_ab = ε_a ι_b + ι_a ε_b`. -/
def Tx' (a b : Fin n) : Module.End R (Finset (Fin n) → R) := εx a * ιx b + ιx a * εx b

/-- `J_a J_b = T'_ab + ε_a ε_b + ι_a ι_b` for all `a, b`. -/
theorem Jx_mul_Jx' (a b : Fin n) :
    Jx (R := R) a * Jx b = Tx' a b + εx a * εx b + ιx a * ιx b := by
  simp only [Jx, Tx', add_mul, mul_add]
  abel

/-- `T'_ab = T_ab` for `a ≠ b` and `T'_aa = 1`. -/
theorem Tx'_eq (a b : Fin n) : Tx' (R := R) a b = if a = b then 1 else Tx a b := by
  split_ifs with h
  · subst h
    exact εx_ιx_self a
  · rw [Tx', Tx, ιx_εx_ne (Ne.symm h), sub_eq_add_neg]

/-! ## The number of directions -/

/-- **The number of directions:** `N f_S = |S| f_S`. -/
def Nx : Module.End R (Finset (Fin n) → R) where
  toFun v T := (T.card : R) * v T
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem Nx_apply (v : Finset (Fin n) → R) (T : Finset (Fin n)) : Nx v T = (T.card : R) * v T :=
  rfl

theorem εx_ιx_apply (a : Fin n) (v : Finset (Fin n) → R) (T : Finset (Fin n)) :
    ((εx a * ιx a : Module.End R (Finset (Fin n) → R)) v) T = if a ∈ T then v T else 0 := by
  simp only [Module.End.mul_apply, εx_apply, ιx_apply]
  by_cases ha : a ∈ T
  · simp only [ha, Finset.notMem_erase, ↓reduceIte, Finset.insert_erase ha]
    rw [← mul_assoc, extSign_mul_self, one_mul]
  · simp [ha]

/-- `N = Σ_a ε_a ι_a`. -/
theorem Nx_eq_sum : (Nx : Module.End R (Finset (Fin n) → R)) = ∑ a, εx a * ιx a := by
  refine LinearMap.ext fun v => funext fun T => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply, Nx_apply]
  simp only [εx_ιx_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **One direction more raises the number by one:** `N ε_a = ε_a (N + 1)`. -/
theorem Nx_εx (a : Fin n) : Nx * εx (R := R) a = εx a * (Nx + 1) := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Nx_apply,
    εx_apply, Pi.add_apply]
  by_cases ha : a ∈ T
  · simp only [ha, ↓reduceIte]
    rw [Finset.card_erase_of_mem ha]
    have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
    push_cast [h1]
    ring
  · simp [ha]

/-- **One direction fewer lowers the number by one:** `N ι_a = ι_a (N − 1)`. -/
theorem Nx_ιx (a : Fin n) : Nx * ιx (R := R) a = ιx a * (Nx - 1) := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, Nx_apply,
    ιx_apply, Pi.sub_apply]
  by_cases ha : a ∈ T
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    ring

/-- **The parallel rotation keeps the number of directions.** -/
theorem Nx_Tx (a b : Fin n) : Nx * Tx (R := R) a b = Tx a b * Nx := by
  have h1 : ∀ c d : Fin n, Nx * (εx (R := R) c * ιx d) = εx c * ιx d * Nx := by
    intro c d
    rw [← mul_assoc, Nx_εx, mul_assoc, add_mul, one_mul, Nx_ιx, mul_sub, mul_one,
      sub_add_cancel, ← mul_assoc]
  rw [Tx, mul_sub, sub_mul, h1, h1]

/-! ## The parallel rotation turns the plane -/

theorem εx_ιx_comm_ne {a b : Fin n} (hab : a ≠ b) :
    εx (R := R) a * ιx b = -(ιx b * εx a) :=
  eq_neg_of_add_eq_zero_left (εx_ιx_ne hab)

/-- **`[T_ab, ε_c] = δ_bc ε_a − δ_ac ε_b`.** -/
theorem Tx_εx (a b c : Fin n) :
    Tx (R := R) a b * εx c - εx c * Tx a b =
      (if b = c then εx a else 0) - (if a = c then εx b else 0) := by
  have key : ∀ x y : Fin n, εx (R := R) x * ιx y * εx c - εx c * (εx x * ιx y) =
      if y = c then εx x else 0 := by
    intro x y
    have h1 : ιx (R := R) y * εx c = (if c = y then 1 else 0) - εx c * ιx y := by
      rw [← εx_ιx_add c y]
      abel
    have h2 : εx (R := R) c * εx x = -(εx x * εx c) := εx_εx_ne x c
    rw [mul_assoc, h1, mul_sub, ← mul_assoc, ← mul_assoc, h2, neg_mul]
    by_cases hyc : y = c
    · subst hyc
      simp only [↓reduceIte, mul_one]
      abel
    · have hcy : ¬c = y := fun h => hyc h.symm
      simp only [hyc, hcy, ↓reduceIte, mul_zero]
      abel
  rw [Tx, sub_mul, mul_sub, sub_sub_sub_comm, key, key]

/-- **`[T_ab, ι_c] = δ_bc ι_a − δ_ac ι_b`.** -/
theorem Tx_ιx (a b c : Fin n) :
    Tx (R := R) a b * ιx c - ιx c * Tx a b =
      (if b = c then ιx a else 0) - (if a = c then ιx b else 0) := by
  have key : ∀ x y : Fin n, εx (R := R) x * ιx y * ιx c - ιx c * (εx x * ιx y) =
      -(if x = c then ιx y else 0) := by
    intro x y
    have h1 : ιx (R := R) c * εx x = (if x = c then 1 else 0) - εx x * ιx c := by
      rw [← εx_ιx_add x c]
      abel
    have h2 : ιx (R := R) y * ιx c = -(ιx c * ιx y) := ιx_ιx_ne c y
    rw [← mul_assoc, h1, sub_mul, mul_assoc, h2]
    split_ifs with hxc
    · rw [one_mul, mul_neg, mul_assoc]
      abel
    · rw [zero_mul, zero_sub, mul_neg, mul_assoc, neg_zero]
      abel
  rw [Tx, sub_mul, mul_sub, sub_sub_sub_comm, key, key]
  split_ifs <;> abel

/-- **The parallel rotation turns the vertical step:** `[T_ab, J_c] = δ_bc J_a − δ_ac J_b`. -/
theorem Tx_Jx (a b c : Fin n) :
    Tx (R := R) a b * Jx c - Jx c * Tx a b =
      (if b = c then Jx a else 0) - (if a = c then Jx b else 0) := by
  have h1 := Tx_εx (R := R) a b c
  have h2 := Tx_ιx (R := R) a b c
  rw [Jx, mul_add, add_mul]
  calc Tx a b * εx c + Tx a b * ιx c - (εx c * Tx a b + ιx c * Tx a b)
      = (Tx a b * εx c - εx c * Tx a b) + (Tx a b * ιx c - ιx c * Tx a b) := by abel
    _ = _ := by
      rw [h1, h2]
      simp only [Jx]
      split_ifs <;> abel

/-! ## Products of anticommuting involutions -/

/-- An element that anticommutes with every factor of a product passes it with a sign. -/
theorem mul_prod_anticomm {A : Type*} [Ring A] (x : A) (l : List A)
    (h : ∀ y ∈ l, x * y = -(y * x)) : x * l.prod = (-1) ^ l.length * (l.prod * x) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.prod_cons, ← mul_assoc, h y (List.mem_cons_self), neg_mul, mul_assoc,
      ih (fun z hz => h z (List.mem_cons_of_mem y hz)), List.length_cons, pow_succ]
    have hc : Commute ((-1 : A) ^ l.length) y := (Commute.neg_one_left y).pow_left _
    rw [← mul_assoc y, ← hc.eq]
    simp only [mul_neg, neg_mul, mul_one, mul_assoc]

/-- **The square of a product of anticommuting involutions** is `(−1)^{C(m,2)}`. -/
theorem prod_sq_anticomm {A : Type*} [Ring A] (l : List A) (hsq : ∀ y ∈ l, y * y = 1)
    (hpair : l.Pairwise fun y z => y * z = -(z * y)) :
    l.prod * l.prod = (-1) ^ (l.length.choose 2) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.pairwise_cons] at hpair
    have h1 : y * l.prod = (-1) ^ l.length * (l.prod * y) :=
      mul_prod_anticomm y l hpair.1
    have hsq' : ∀ z ∈ l, z * z = 1 := fun z hz => hsq z (List.mem_cons_of_mem y hz)
    have ih' := ih hsq' hpair.2
    have hc : Commute ((-1 : A) ^ l.length) y := (Commute.neg_one_left y).pow_left _
    have hc' : Commute ((-1 : A) ^ l.length) l.prod := (Commute.neg_one_left _).pow_left _
    rw [List.prod_cons, List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right, pow_add,
      ← ih']
    calc y * l.prod * (y * l.prod) = y * (l.prod * y) * l.prod := by
          simp only [mul_assoc]
      _ = y * ((-1) ^ l.length * (y * l.prod)) * l.prod := by
          congr 2
          rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
          simp
      _ = (-1) ^ l.length * (y * y) * (l.prod * l.prod) := by
          rw [← mul_assoc y, ← hc.eq]
          simp only [mul_assoc]
      _ = (-1) ^ l.length * (l.prod * l.prod) := by
          rw [hsq y List.mem_cons_self, mul_one]

end General

/-! ## On the six: 64 dimensions, the volume element and the square root of the sign -/

section Six

/-- The exterior algebra of the six has dimension `64`. -/
theorem finrank_ext_six (R : Type*) [Field R] :
    Module.finrank R (Finset (Fin 6) → R) = 64 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_fin]
  norm_num

variable {R : Type*} [CommRing R]

/-- The six vertical steps in order. -/
def Jlist : List (Module.End R (Finset (Fin 6) → R)) := List.ofFn fun a : Fin 6 => Jx a

/-- **The volume element** `w = J₀ J₁ J₂ J₃ J₄ J₅`. -/
def volume : Module.End R (Finset (Fin 6) → R) := (Jlist (R := R)).prod

theorem Jlist_pairwise : (Jlist (R := R)).Pairwise fun y z => y * z = -(z * y) := by
  rw [Jlist, List.pairwise_ofFn]
  intro i j hij
  exact Jx_anticomm (ne_of_lt hij)

/-- **The volume element squares to `−1`:** `(J₀ ⋯ J₅)² = −1`. -/
theorem volume_sq : volume (R := R) * volume = -1 := by
  rw [volume, prod_sq_anticomm _ ?_ Jlist_pairwise]
  · rw [Jlist, List.length_ofFn, show Nat.choose 6 2 = 15 from rfl]
    norm_num
  · intro y hy
    rw [Jlist, List.mem_ofFn] at hy
    obtain ⟨a, rfl⟩ := hy
    exact Jx_mul_self a

end Six

section Half

/-- **The vertical step with the square root of the sign** of the division `D`: `f_x = i^{[x ∈ D]} J_x`. -/
noncomputable def halfStep (D : Finset (Fin 6)) (x : Fin 6) :
    Module.End ℂ (Finset (Fin 6) → ℂ) :=
  (if x ∈ D then Complex.I else 1) • Jx x

/-- **The divided steps square to `−1`:** `f_x² = θ_D(x)`. -/
theorem half_mul_self (D : Finset (Fin 6)) (x : Fin 6) :
    halfStep D x * halfStep D x = (if x ∈ D then -1 else 1 : ℂ) • 1 := by
  simp only [halfStep, smul_mul_smul_comm, Jx_mul_self]
  by_cases h : x ∈ D
  · simp only [h, ↓reduceIte, Complex.I_mul_I]
  · simp only [h, ↓reduceIte, mul_one]

/-- Steps along different directions still anticommute with the square root of the sign. -/
theorem half_anticomm_ne (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    halfStep D x * halfStep D y = -(halfStep D y * halfStep D x) := by
  simp only [halfStep, smul_mul_smul_comm, Jx_anticomm hxy, smul_neg]
  rw [mul_comm]

/-- **`f_x f_y + f_y f_x = 2 θ_D(x) δ_xy`:** the square root of the sign makes the divided steps square to `−1`. -/
theorem half_anticomm (D : Finset (Fin 6)) (x y : Fin 6) :
    halfStep D x * halfStep D y + halfStep D y * halfStep D x =
      if x = y then (2 * (if x ∈ D then -1 else 1) : ℂ) • 1 else 0 := by
  by_cases hxy : x = y
  · subst hxy
    rw [half_mul_self, ← two_smul ℂ, smul_smul, if_pos rfl]
  · rw [half_anticomm_ne D hxy, neg_add_cancel, if_neg hxy]

theorem filter_finRange_length (D : Finset (Fin 6)) :
    ((List.finRange 6).filter fun b => decide (b ∈ D)).length = D.card := by
  revert D
  decide +kernel

/-- **The half on the whole:** `f₀ f₁ ⋯ f₅ = i^{|D|} J₀ J₁ ⋯ J₅`. -/
theorem half_prod (D : Finset (Fin 6)) :
    (List.ofFn (halfStep D)).prod = Complex.I ^ D.card • volume := by
  have h : ∀ l : List (Fin 6), (l.map (halfStep D)).prod =
      (l.map fun x => if x ∈ D then Complex.I else 1).prod • (l.map Jx).prod := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, ih, halfStep, smul_mul_smul_comm]
  have hl : List.ofFn (halfStep D) = (List.finRange 6).map (halfStep D) := by
    rw [List.ofFn_eq_map]
  rw [hl, h, volume, Jlist, List.ofFn_eq_map]
  congr 1
  rw [List.prod_map_ite, List.map_const', List.prod_replicate, List.map_const', List.prod_replicate,
    one_pow, mul_one]
  congr 1
  exact filter_finRange_length D

end Half

end Comparison

end
