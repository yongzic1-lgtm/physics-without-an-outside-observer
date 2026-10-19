import Mathlib

/-!
# The centres `Y`, `Q`, and `S(U(3) × U(2)) ≅ (SU(3) × SU(2) × U(1))/ℤ₆` (Prop. 46)

On `ℂ⁵ = C ⊕ F`, `C = {0, 1, 2}` the colour lines and `F = {h, k} = {3, 4}` the plane
(`Existence/Commutant.lean`: `crossP`, `lastDirectionP`, `finrank_plane5 = 12`, `finrank_lastDirection5 = 9`):

* `plane_centre`: **the rotations of `s(u(3) ⊕ u(2))` that commute with all of it are `ℝ·iY`**,
  `Y = diag(−⅓, −⅓, −⅓, ½, ½)`; `Yc_plane`, `Yc_central`: and `iY` is one of them.
* `lastDirection_centre`: **the centre of `su(3) ⊕ u(1)` (those keeping also `ℓ_h`) is `ℝ·iQ`**,
  `Q = diag(−⅓, −⅓, −⅓, 0, 1) = N_k − N_C/3`; `Qc_lastDirection`, `Qc_central`.
* In the basis of the two-spinor states (the sixteen even sets `S`, on which `Σ_s y_s ε_sι_s` acts by
  `Σ_{s∈S} y_s`, `Existence/Exterior.lean`: `εx_ιx_apply`): `chargeOp_single`; `trY`, `trY3`:
  `Tr Y = Tr Y³ = 0`; `trY_colour`: `2·⅙ − ⅔ + ⅓ = 0` over the colour triplets and antitriplets;
  `trY_weak`: `3·⅙ − ½ = 0` over the weak doublets; `lastDirection_neutral`: `Q(ℓ_h) = 0`.
* `sym_hom`, `sym_surjective`, `sym_ker`: **`(A, B, z) ↦ (z²A, z̄³B)` maps
  `SU(3) × SU(2) × U(1)` onto `S(U(3) × U(2))` with kernel the six `(z̄²·1, z³·1, z)`, `z⁶ = 1`**;
  `sym_quotient`: `(SU(3) × SU(2) × U(1)) ⧸ ker ≃* S(U(3) × U(2))`; `ker_card`, `ker_cyclic`:
  the kernel is cyclic of order six, `ℤ₆`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Complex

noncomputable section

/-! ## The two centres -/

/-- An entry across the plane: one index in `C = {0, 1, 2}`, the other in `F = {3, 4}`. -/
def cross5 (s t : Fin 5) : Prop := ((s : ℕ) < 3 ∧ 3 ≤ (t : ℕ)) ∨ (3 ≤ (s : ℕ) ∧ (t : ℕ) < 3)

instance : DecidableRel cross5 := fun s t => by unfold cross5; infer_instance

/-- `s(u(3) ⊕ u(2))`: anti-Hermitian, trace zero, nothing across the plane. -/
def IsPlaneTurn (Z : Matrix (Fin 5) (Fin 5) ℂ) : Prop :=
  Zᴴ = -Z ∧ Z.trace = 0 ∧ ∀ s t, cross5 s t → Z s t = 0

/-- `su(3) ⊕ u(1)`: a plane rotation that also keeps `ℓ_h`: no `(h,h)`, `(h,k)`, `(k,h)` entries. -/
def IsLastDirectionTurn (Z : Matrix (Fin 5) (Fin 5) ℂ) : Prop :=
  IsPlaneTurn Z ∧ Z 3 3 = 0 ∧ Z 3 4 = 0 ∧ Z 4 3 = 0

/-- The hypercharge `Y = diag(−⅓, −⅓, −⅓, ½, ½)`, as the rotation `iY`. -/
def yv : Fin 5 → ℂ := ![-1 / 3, -1 / 3, -1 / 3, 1 / 2, 1 / 2]

/-- The charge `Q = diag(−⅓, −⅓, −⅓, 0, 1)`, as the rotation `iQ`. -/
def qv : Fin 5 → ℂ := ![-1 / 3, -1 / 3, -1 / 3, 0, 1]

def Yc : Matrix (Fin 5) (Fin 5) ℂ := diagonal fun s => I * yv s

def Qc : Matrix (Fin 5) (Fin 5) ℂ := diagonal fun s => I * qv s

/-- The test rotations `E_st − E_ts` and `i(E_st + E_ts)`. -/
def tA (s t : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.single s t 1 - Matrix.single t s 1

def tB (s t : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ := I • (Matrix.single s t 1 + Matrix.single t s 1)

theorem tr_single (s t : Fin 5) :
    (Matrix.single s t (1 : ℂ)).trace = if s = t then 1 else 0 := by
  fin_cases s <;> fin_cases t <;> simp [Matrix.trace, Matrix.single_apply, Fin.sum_univ_five]

theorem tA_plane (s t : Fin 5) (hst : s ≠ t) (hc : ¬cross5 s t) : IsPlaneTurn (tA s t) := by
  have hc' : ¬cross5 t s := by unfold cross5 at hc ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [tA, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.single_apply,
      Matrix.neg_apply]
    split_ifs <;> simp_all
  · rw [tA, Matrix.trace_sub, tr_single, tr_single]
    simp [hst, Ne.symm hst]
  · intro i j hij
    simp only [tA, Matrix.sub_apply, Matrix.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h1.1 ▸ h1.2 ▸ hij) hc
    · exact absurd (h1.1 ▸ h1.2 ▸ hij) hc
    · exact absurd (h2.1 ▸ h2.2 ▸ hij) hc'
    · simp

theorem tB_plane (s t : Fin 5) (hst : s ≠ t) (hc : ¬cross5 s t) : IsPlaneTurn (tB s t) := by
  have hc' : ¬cross5 t s := by unfold cross5 at hc ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [tB, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.single_apply, Matrix.neg_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · rw [tB, Matrix.trace_smul, Matrix.trace_add, tr_single, tr_single]
    simp [hst, Ne.symm hst]
  · intro i j hij
    simp only [tB, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs with h1 h2 h2
    · exact absurd (h1.1 ▸ h1.2 ▸ hij) hc
    · exact absurd (h1.1 ▸ h1.2 ▸ hij) hc
    · exact absurd (h2.1 ▸ h2.2 ▸ hij) hc'
    · simp

/-- Commuting with the two test rotations of a pair forces equal diagonal entries and a zero entry. -/
theorem comm_tests (Z : Matrix (Fin 5) (Fin 5) ℂ) (s t : Fin 5) (hst : s ≠ t)
    (hA : Z * tA s t = tA s t * Z) (hB : Z * tB s t = tB s t * Z) :
    Z s s = Z t t ∧ Z s t = 0 := by
  have e1 : Z s s = Z t t := by
    have := congrFun (congrFun hA s) t
    simpa [tA, Matrix.mul_sub, Matrix.sub_mul, hst, Ne.symm hst] using this
  have e2 : -Z s t = Z t s := by
    have := congrFun (congrFun hA s) s
    simpa [tA, Matrix.mul_sub, Matrix.sub_mul, hst, Ne.symm hst] using this
  have e3 : Z s t = Z t s := by
    have h := congrFun (congrFun hB s) s
    simp [tB, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hst,
      Ne.symm hst] at h
    have h' : I * (Z s t - Z t s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 I_ne_zero
    · exact sub_eq_zero.1 h0
  refine ⟨e1, ?_⟩
  have h2 : (2 : ℂ) * Z s t = 0 := by linear_combination e3 - e2
  simpa using h2

theorem antiherm_entry {Z : Matrix (Fin 5) (Fin 5) ℂ} (hH : Zᴴ = -Z) (i j : Fin 5)
    (h : Z i j = 0) : Z j i = 0 := by
  have := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, h, neg_zero, star_eq_zero] at this
  exact this

theorem antiherm_diag {Z : Matrix (Fin 5) (Fin 5) ℂ} (hH : Zᴴ = -Z) (i : Fin 5) :
    Z i i = I * ((Z i i).im : ℂ) := by
  have := congrFun (congrFun hH i) i
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hre : (Z i i).re = 0 := by
    have := congrArg Complex.re this
    simp at this
    linarith
  apply Complex.ext <;> simp [hre]

theorem trace5 (Z : Matrix (Fin 5) (Fin 5) ℂ) :
    Z.trace = Z 0 0 + Z 1 1 + Z 2 2 + Z 3 3 + Z 4 4 := by
  simp [Matrix.trace, Fin.sum_univ_five]

/-- **`iY` is a plane rotation** and **it commutes with every plane rotation.** -/
theorem Yc_plane : IsPlaneTurn Yc := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Yc, yv, Matrix.conjTranspose_apply, Matrix.diagonal]
  · rw [trace5]
    simp [Yc, yv]
    ring
  · intro s t h
    have hne : s ≠ t := by rintro rfl; unfold cross5 at h; omega
    simp [Yc, Matrix.diagonal_apply_ne _ hne]

theorem Yc_central (W : Matrix (Fin 5) (Fin 5) ℂ) (hW : IsPlaneTurn W) : Yc * W = W * Yc := by
  obtain ⟨-, -, hx⟩ := hW
  ext i j
  simp only [Yc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : cross5 i j
  · rw [hx i j h]; ring
  · have : yv i = yv j := by
      fin_cases i <;> fin_cases j <;> simp_all [cross5, yv]
    rw [this]; ring

/-- **The centre of `s(u(3) ⊕ u(2))` is `ℝ·iY`.** -/
theorem plane_centre (Z : Matrix (Fin 5) (Fin 5) ℂ) (hZ : IsPlaneTurn Z)
    (hc : ∀ W, IsPlaneTurn W → Z * W = W * Z) : ∃ a : ℝ, Z = (a : ℂ) • Yc := by
  have T : ∀ s t : Fin 5, s ≠ t → ¬cross5 s t → Z s s = Z t t ∧ Z s t = 0 :=
    fun s t hst hcr => comm_tests Z s t hst (hc _ (tA_plane s t hst hcr))
      (hc _ (tB_plane s t hst hcr))
  obtain ⟨hH, htr, hx⟩ := hZ
  obtain ⟨d01, z01⟩ := T 0 1 (by decide) (by decide)
  obtain ⟨d02, z02⟩ := T 0 2 (by decide) (by decide)
  obtain ⟨-, z12⟩ := T 1 2 (by decide) (by decide)
  obtain ⟨d34, z34⟩ := T 3 4 (by decide) (by decide)
  have z10 := antiherm_entry hH 0 1 z01
  have z20 := antiherm_entry hH 0 2 z02
  have z21 := antiherm_entry hH 1 2 z12
  have z43 := antiherm_entry hH 3 4 z34
  have c03 := hx 0 3 (by decide)
  have c04 := hx 0 4 (by decide)
  have c13 := hx 1 3 (by decide)
  have c14 := hx 1 4 (by decide)
  have c23 := hx 2 3 (by decide)
  have c24 := hx 2 4 (by decide)
  have c30 := hx 3 0 (by decide)
  have c40 := hx 4 0 (by decide)
  have c31 := hx 3 1 (by decide)
  have c41 := hx 4 1 (by decide)
  have c32 := hx 3 2 (by decide)
  have c42 := hx 4 2 (by decide)
  rw [trace5] at htr
  have h33 : Z 3 3 = -(3 / 2 : ℂ) * Z 0 0 := by
    rw [← d01, ← d02, ← d34] at htr
    linear_combination htr / 2
  have h00 := antiherm_diag hH 0
  set a := (Z 0 0).im with ha
  refine ⟨-3 * a, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yc, yv, Matrix.diagonal, z01, z02, z12, z34, z10, z20, z21, z43, c03, c04, c13, c14,
      c23, c24, c30, c40, c31, c41, c32, c42] <;>
    first
    | (rw [← d01, h00]; push_cast; ring)
    | (rw [← d02, h00]; push_cast; ring)
    | (rw [h00]; push_cast; ring)
    | (rw [← d34, h33, h00]; push_cast; ring)
    | (rw [h33, h00]; push_cast; ring)

/-- **`iQ` keeps `ℓ_h`** and **commutes with every rotation of `su(3) ⊕ u(1)`.** -/
theorem Qc_lastDirection : IsLastDirectionTurn Qc := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Qc, qv, Matrix.conjTranspose_apply, Matrix.diagonal]
  · rw [trace5]
    simp [Qc, qv]
    ring
  · intro s t h
    have hne : s ≠ t := by rintro rfl; unfold cross5 at h; omega
    simp [Qc, Matrix.diagonal_apply_ne _ hne]
  · simp [Qc, qv]
  · simp [Qc]
  · simp [Qc]

theorem Qc_central (W : Matrix (Fin 5) (Fin 5) ℂ) (hW : IsLastDirectionTurn W) : Qc * W = W * Qc := by
  obtain ⟨⟨-, -, hx⟩, h33, h34, h43⟩ := hW
  ext i j
  simp only [Qc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : cross5 i j
  · rw [hx i j h]; ring
  · fin_cases i <;> fin_cases j <;> simp_all [cross5, qv] <;> ring

/-- **The centre of `su(3) ⊕ u(1)` is `ℝ·iQ`**, `Q = N_k − N_C/3`. -/
theorem lastDirection_centre (Z : Matrix (Fin 5) (Fin 5) ℂ) (hZ : IsLastDirectionTurn Z)
    (hc : ∀ W, IsLastDirectionTurn W → Z * W = W * Z) : ∃ a : ℝ, Z = (a : ℂ) • Qc := by
  have hand_of_face : ∀ s t : Fin 5, (s : ℕ) < 3 → (t : ℕ) < 3 → s ≠ t →
      IsLastDirectionTurn (tA s t) ∧ IsLastDirectionTurn (tB s t) := by
    intro s t hs ht hst
    have hcr : ¬cross5 s t := by unfold cross5; omega
    have h3s : (3 : Fin 5) ≠ s := fun h => by rw [← h] at hs; simp at hs
    have h3t : (3 : Fin 5) ≠ t := fun h => by rw [← h] at ht; simp at ht
    have h4s : (4 : Fin 5) ≠ s := fun h => by rw [← h] at hs; simp at hs
    have h4t : (4 : Fin 5) ≠ t := fun h => by rw [← h] at ht; simp at ht
    refine ⟨⟨tA_plane s t hst hcr, ?_, ?_, ?_⟩, ⟨tB_plane s t hst hcr, ?_, ?_, ?_⟩⟩ <;>
      simp [tA, tB, Matrix.single_apply, h3s, h3t, h4s, h4t, h3s.symm, h3t.symm, h4s.symm,
        h4t.symm]
  have T : ∀ s t : Fin 5, (s : ℕ) < 3 → (t : ℕ) < 3 → s ≠ t → Z s s = Z t t ∧ Z s t = 0 :=
    fun s t hs ht hst => comm_tests Z s t hst (hc _ (hand_of_face s t hs ht hst).1)
      (hc _ (hand_of_face s t hs ht hst).2)
  obtain ⟨⟨hH, htr, hx⟩, h33, h34, h43⟩ := hZ
  obtain ⟨d01, z01⟩ := T 0 1 (by decide) (by decide) (by decide)
  obtain ⟨d02, z02⟩ := T 0 2 (by decide) (by decide) (by decide)
  obtain ⟨-, z12⟩ := T 1 2 (by decide) (by decide) (by decide)
  have z10 := antiherm_entry hH 0 1 z01
  have z20 := antiherm_entry hH 0 2 z02
  have z21 := antiherm_entry hH 1 2 z12
  have c03 := hx 0 3 (by decide)
  have c04 := hx 0 4 (by decide)
  have c13 := hx 1 3 (by decide)
  have c14 := hx 1 4 (by decide)
  have c23 := hx 2 3 (by decide)
  have c24 := hx 2 4 (by decide)
  have c30 := hx 3 0 (by decide)
  have c40 := hx 4 0 (by decide)
  have c31 := hx 3 1 (by decide)
  have c41 := hx 4 1 (by decide)
  have c32 := hx 3 2 (by decide)
  have c42 := hx 4 2 (by decide)
  rw [trace5, ← d01, ← d02, h33] at htr
  have h44 : Z 4 4 = -3 * Z 0 0 := by linear_combination htr
  have h00 := antiherm_diag hH 0
  set a := (Z 0 0).im with ha
  refine ⟨-3 * a, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qc, qv, Matrix.diagonal, z01, z02, z12, z10, z20, z21, c03, c04, c13, c14,
      c23, c24, c30, c40, c31, c41, c32, c42, h33, h34, h43] <;>
    first
    | (rw [← d01, h00]; push_cast; ring)
    | (rw [← d02, h00]; push_cast; ring)
    | (rw [h00]; push_cast; ring)
    | (rw [h44, h00]; push_cast; ring)

/-! ## In the basis of the two-spinor states -/

/-- The two-spinor states: the sixteen even sets of lines. -/
def relSets : Finset (Finset (Fin 5)) := Finset.univ.filter fun S => Even S.card

theorem card_relSets : relSets.card = 16 := by decide

/-- The charges of a two-spinor state, scaled to integers: `6Y` and `3Q` summed over `S`. -/
def chargeZ (y : Fin 5 → ℤ) (S : Finset (Fin 5)) : ℤ := ∑ s ∈ S, y s

/-- `6Y = diag(−2, −2, −2, 3, 3)`. -/
def y6 : Fin 5 → ℤ := ![-2, -2, -2, 3, 3]

/-- `3Q = diag(−1, −1, −1, 0, 3)`. -/
def q3 : Fin 5 → ℤ := ![-1, -1, -1, 0, 3]

/-- The diagonal operator `Σ_s y_s N_s` on the two-spinor states (`N_s = ε_sι_s`). -/
def chargeOp (y : Fin 5 → ℂ) : Module.End ℂ (Finset (Fin 5) → ℂ) where
  toFun v T := (∑ s ∈ T, y s) * v T
  map_add' v w := by funext T; simp [mul_add]
  map_smul' c v := by funext T; simp; ring

/-- **The centre acts on each two-spinor state `f_S` by `Σ_{s ∈ S} y_s`.** -/
theorem chargeOp_single (y : Fin 5 → ℂ) (S : Finset (Fin 5)) :
    chargeOp y (Pi.single S 1) = (∑ s ∈ S, y s) • Pi.single S 1 := by
  funext T
  by_cases h : T = S
  · subst h; simp [chargeOp]
  · simp [chargeOp, Pi.single_apply, h]

/-- **`Tr Y = 0` over the sixteen.** -/
theorem trY : ∑ S ∈ relSets, chargeZ y6 S = 0 := by decide

/-- **`Tr Y³ = 0` over the sixteen.** -/
theorem trY3 : ∑ S ∈ relSets, chargeZ y6 S ^ 3 = 0 := by decide

/-- **Colour triplets and antitriplets with `Y`: `2·⅙ − ⅔ + ⅓ = 0`.** -/
theorem trY_colour :
    ∑ S ∈ relSets.filter (fun S => (S.filter fun s : Fin 5 => s.val < 3).card = 1 ∨
      (S.filter fun s : Fin 5 => s.val < 3).card = 2), chargeZ y6 S = 0 := by decide

/-- **Weak doublets with `Y`: `3·⅙ − ½ = 0`.** -/
theorem trY_weak :
    ∑ S ∈ relSets.filter (fun S => (3 ∈ S ∧ 4 ∉ S) ∨ (3 ∉ S ∧ 4 ∈ S)), chargeZ y6 S = 0 := by
  decide

/-- `ℓ_h = f_{C ∪ {k}}` is neutral. -/
theorem lastDirection_neutral : chargeZ q3 {0, 1, 2, 4} = 0 := by decide

/-- The hypercharges of the sixteen: `0` (the singlet), `−⅔` three times, `⅙` six times, `1`, `⅓`
three times, `−½` twice (here times six). -/
theorem hypercharge_table :
    (relSets.filter fun S => chargeZ y6 S = 0).card = 1 ∧
    (relSets.filter fun S => chargeZ y6 S = -4).card = 3 ∧
    (relSets.filter fun S => chargeZ y6 S = 1).card = 6 ∧
    (relSets.filter fun S => chargeZ y6 S = 6).card = 1 ∧
    (relSets.filter fun S => chargeZ y6 S = 2).card = 3 ∧
    (relSets.filter fun S => chargeZ y6 S = -3).card = 2 := by decide

/-! ## `S(U(3) × U(2)) ≅ (SU(3) × SU(2) × U(1))/ℤ₆` -/

abbrev U3 := Matrix.unitaryGroup (Fin 3) ℂ
abbrev U2 := Matrix.unitaryGroup (Fin 2) ℂ
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev U1 := unitary ℂ

/-- **`S(U(3) × U(2))`**: pairs of rotations whose determinants multiply to one. -/
def SU32 : Subgroup (U3 × U2) where
  carrier := {g | (g.1 : Matrix (Fin 3) (Fin 3) ℂ).det * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).det = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    change ((a.1 : Matrix (Fin 3) (Fin 3) ℂ) * b.1).det *
      ((a.2 : Matrix (Fin 2) (Fin 2) ℂ) * b.2).det = 1
    rw [Matrix.det_mul, Matrix.det_mul]
    linear_combination ((b.1 : Matrix (Fin 3) (Fin 3) ℂ).det *
      (b.2 : Matrix (Fin 2) (Fin 2) ℂ).det) * ha + hb
  one_mem' := by
    change (1 : Matrix (Fin 3) (Fin 3) ℂ).det * (1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    change (star (a.1 : Matrix (Fin 3) (Fin 3) ℂ)).det *
      (star (a.2 : Matrix (Fin 2) (Fin 2) ℂ)).det = 1
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,
      Matrix.det_conjTranspose, ← star_mul', ha, star_one]

theorem smul_mem_unitary {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) (hc : star c * c = 1)
    (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ) : c • A ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hA, smul_smul, mul_comm c, hc, one_smul]

theorem u1_star_mul (z : U1) : star (z : ℂ) * z = 1 := Unitary.star_mul_self_of_mem z.2

theorem u1_mul_star (z : U1) : (z : ℂ) * star (z : ℂ) = 1 := Unitary.mul_star_self_of_mem z.2

theorem pow_star_mul (z : U1) (k : ℕ) : star ((z : ℂ) ^ k) * (z : ℂ) ^ k = 1 := by
  rw [star_pow, ← mul_pow, u1_star_mul, one_pow]

theorem star_pow_star_mul (z : U1) (k : ℕ) :
    star (star (z : ℂ) ^ k) * star (z : ℂ) ^ k = 1 := by
  rw [star_pow, star_star, ← mul_pow, u1_mul_star, one_pow]

/-- The first factor `z²A`. -/
def sym1 (x : SU3 × SU2 × U1) : U3 :=
  ⟨((x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ),
    smul_mem_unitary _ (pow_star_mul x.2.2 2) _ x.1.2.1⟩

/-- The second factor `z̄³B`. -/
def sym2 (x : SU3 × SU2 × U1) : U2 :=
  ⟨(star (x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ),
    smul_mem_unitary _ (star_pow_star_mul x.2.2 3) _ x.2.1.2.1⟩

theorem sym_mem (x : SU3 × SU2 × U1) : (sym1 x, sym2 x) ∈ SU32 := by
  change ((((x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ)).det *
    ((star (x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ)).det) = 1
  have h1 : (x.1 : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := x.1.2.2
  have h2 : (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := x.2.1.2.2
  rw [Matrix.det_smul, Matrix.det_smul, h1, h2]
  simp only [Fintype.card_fin, mul_one]
  rw [← pow_mul, ← pow_mul, ← mul_pow, u1_mul_star, one_pow]

/-- **`(A, B, z) ↦ (z²A, z̄³B)` is a homomorphism `SU(3) × SU(2) × U(1) → S(U(3) × U(2))`.** -/
def symHom : SU3 × SU2 × U1 →* SU32 where
  toFun x := ⟨(sym1 x, sym2 x), sym_mem x⟩
  map_one' := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change ((1 : ℂ) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1
      simp
    · change (star (1 : ℂ) ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
      simp
  map_mul' x y := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (((x.2.2 : ℂ) * y.2.2) ^ 2) • ((x.1 : Matrix (Fin 3) (Fin 3) ℂ) * y.1) =
        (((x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ)) *
          (((y.2.2 : ℂ) ^ 2) • (y.1 : Matrix (Fin 3) (Fin 3) ℂ))
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_pow, mul_comm]
    · change (star ((x.2.2 : ℂ) * y.2.2) ^ 3) • ((x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * y.2.1) =
        ((star (x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          ((star (y.2.2 : ℂ) ^ 3) • (y.2.1 : Matrix (Fin 2) (Fin 2) ℂ))
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul', mul_pow, mul_comm]

theorem norm_eq_one_of_pow {z d : ℂ} (h : z ^ 6 = d) (hd : ‖d‖ = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ 6 = 1 := by rw [← norm_pow, h, hd]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by norm_num)).1 this

theorem star_mul_of_norm {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

/-- **`(A, B, z) ↦ (z²A, z̄³B)` is onto `S(U(3) × U(2))`.** -/
theorem sym_surjective : Function.Surjective symHom := by
  rintro ⟨⟨P, Q⟩, hPQ⟩
  have hd : star (P : Matrix (Fin 3) (Fin 3) ℂ).det * (P : Matrix (Fin 3) (Fin 3) ℂ).det = 1 :=
    Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary P.2)
  obtain ⟨z0, hz0⟩ := IsAlgClosed.exists_pow_nat_eq (P : Matrix (Fin 3) (Fin 3) ℂ).det
    (by norm_num : 0 < 6)
  have hdn : ‖(P : Matrix (Fin 3) (Fin 3) ℂ).det‖ = 1 := by
    have := congrArg (fun w : ℂ => ‖w‖) hd
    simp only [norm_mul, norm_star, norm_one] at this
    nlinarith [norm_nonneg (P : Matrix (Fin 3) (Fin 3) ℂ).det]
  have hz1 : ‖z0‖ = 1 := norm_eq_one_of_pow hz0 hdn
  have hzs : star z0 * z0 = 1 := star_mul_of_norm hz1
  have hzs' : z0 * star z0 = 1 := by rw [mul_comm]; exact hzs
  let z : U1 := ⟨z0, Unitary.mem_iff.2 ⟨hzs, hzs'⟩⟩
  have hA : ((star z0) ^ 2 • (P : Matrix (Fin 3) (Fin 3) ℂ)) ∈ SU3 := by
    refine ⟨smul_mem_unitary _ ?_ _ P.2, ?_⟩
    · rw [star_pow, star_star, ← mul_pow, hzs', one_pow]
    · change ((star z0) ^ 2 • (P : Matrix (Fin 3) (Fin 3) ℂ)).det = 1
      rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, ← hz0, ← mul_pow, hzs]
      simp
  have hB : (z0 ^ 3 • (Q : Matrix (Fin 2) (Fin 2) ℂ)) ∈ SU2 := by
    refine ⟨smul_mem_unitary _ ?_ _ Q.2, ?_⟩
    · rw [star_pow, ← mul_pow, hzs, one_pow]
    · change (z0 ^ 3 • (Q : Matrix (Fin 2) (Fin 2) ℂ)).det = 1
      rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, hz0]
      exact hPQ
  refine ⟨(⟨_, hA⟩, ⟨_, hB⟩, z), ?_⟩
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (z0 ^ 2) • ((star z0) ^ 2 • (P : Matrix (Fin 3) (Fin 3) ℂ)) = P
    rw [smul_smul, ← mul_pow, hzs', one_pow, one_smul]
  · change (star z0 ^ 3) • (z0 ^ 3 • (Q : Matrix (Fin 2) (Fin 2) ℂ)) = Q
    rw [smul_smul, ← mul_pow, hzs, one_pow, one_smul]

/-- The kernel's elements, from the sixth roots of unity: `ζ ↦ (ζ̄²·1, ζ³·1, ζ)`. -/
def kerElt (ζ : rootsOfUnity 6 ℂ) : SU3 × SU2 × U1 := by
  have h6 : ((ζ : ℂˣ) : ℂ) ^ 6 = 1 := by
    have h := (_root_.mem_rootsOfUnity 6 (ζ : ℂˣ)).1 ζ.2
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
    exact h'
  have hn : ‖((ζ : ℂˣ) : ℂ)‖ = 1 := norm_eq_one_of_pow h6 (by simp)
  have hs : star ((ζ : ℂˣ) : ℂ) * ((ζ : ℂˣ) : ℂ) = 1 := star_mul_of_norm hn
  have hs' : ((ζ : ℂˣ) : ℂ) * star ((ζ : ℂˣ) : ℂ) = 1 := by rw [mul_comm]; exact hs
  exact (⟨(star ((ζ : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ),
      smul_mem_unitary _ (by rw [star_pow, star_star, ← mul_pow, hs', one_pow]) _
        (one_mem _), by
      change ((star ((ζ : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = 1
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul, ← star_pow,
        show 2 * 3 = 6 from rfl, h6, star_one]⟩,
    ⟨((ζ : ℂˣ) : ℂ) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ),
      smul_mem_unitary _ (by rw [star_pow, ← mul_pow, hs, one_pow]) _ (one_mem _), by
      change (((ζ : ℂˣ) : ℂ) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 1
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul,
        show 3 * 2 = 6 from rfl, h6]⟩,
    ⟨((ζ : ℂˣ) : ℂ), Unitary.mem_iff.2 ⟨hs, hs'⟩⟩)

theorem kerElt_third (ζ : rootsOfUnity 6 ℂ) : ((kerElt ζ).2.2 : ℂ) = ((ζ : ℂˣ) : ℂ) := rfl

/-- **The kernel is exactly the six `(ζ̄²·1, ζ³·1, ζ)`, `ζ⁶ = 1`.** -/
theorem sym_ker (x : SU3 × SU2 × U1) :
    symHom x = 1 ↔ ∃ ζ : rootsOfUnity 6 ℂ, x = kerElt ζ := by
  constructor
  · intro h
    have h1 : ((x.2.2 : ℂ) ^ 2) • (x.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
      congrArg (fun g : SU32 => ((g.1.1 : U3) : Matrix (Fin 3) (Fin 3) ℂ)) h
    have h2 : (star (x.2.2 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      congrArg (fun g : SU32 => ((g.1.2 : U2) : Matrix (Fin 2) (Fin 2) ℂ)) h
    set z : ℂ := (x.2.2 : ℂ) with hz
    have hzs : star z * z = 1 := u1_star_mul x.2.2
    have hzs' : z * star z = 1 := u1_mul_star x.2.2
    have hA : (x.1 : Matrix (Fin 3) (Fin 3) ℂ) = (star z) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
      have := congrArg (fun M => (star z) ^ 2 • M) h1
      simp only [smul_smul, ← mul_pow, hzs, one_pow, one_smul] at this
      exact this
    have hB : (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = z ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have := congrArg (fun M => z ^ 3 • M) h2
      simp only [smul_smul, ← mul_pow, hzs', one_pow, one_smul] at this
      exact this
    have h6 : z ^ 6 = 1 := by
      have := x.2.1.2.2
      change (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 at this
      rw [hB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul] at this
      exact this
    have hu : IsUnit z := isUnit_iff_ne_zero.2 (fun h0 => by rw [h0] at h6; norm_num at h6)
    refine ⟨⟨hu.unit, ?_⟩, ?_⟩
    · rw [_root_.mem_rootsOfUnity]
      ext
      simp [h6]
    · refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · exact hA
      · exact hB
      · rfl
  · rintro ⟨ζ, rfl⟩
    have h6 : ((ζ : ℂˣ) : ℂ) ^ 6 = 1 := by
      have h := (_root_.mem_rootsOfUnity 6 (ζ : ℂˣ)).1 ζ.2
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
      exact h'
    have hs : star ((ζ : ℂˣ) : ℂ) * ((ζ : ℂˣ) : ℂ) = 1 :=
      star_mul_of_norm (norm_eq_one_of_pow h6 (by simp))
    have hs' : ((ζ : ℂˣ) : ℂ) * star ((ζ : ℂˣ) : ℂ) = 1 := by rw [mul_comm]; exact hs
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (((ζ : ℂˣ) : ℂ) ^ 2) • ((star ((ζ : ℂˣ) : ℂ)) ^ 2 •
        (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 1
      rw [smul_smul, ← mul_pow, hs', one_pow, one_smul]
    · change (star ((ζ : ℂˣ) : ℂ) ^ 3) • (((ζ : ℂˣ) : ℂ) ^ 3 •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
      rw [smul_smul, ← mul_pow, hs, one_pow, one_smul]

theorem kerElt_injective : Function.Injective kerElt := by
  intro ζ ξ h
  have := congrArg (fun x : SU3 × SU2 × U1 => ((x.2.2 : U1) : ℂ)) h
  simp only [kerElt_third] at this
  exact Subtype.ext (Units.ext this)

theorem kerElt_one : kerElt 1 = 1 := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · change (star (((1 : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1
    simp
  · change (((1 : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    simp
  · change (((1 : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ) = 1
    simp

theorem kerElt_mul (ζ ξ : rootsOfUnity 6 ℂ) : kerElt (ζ * ξ) = kerElt ζ * kerElt ξ := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · change (star (((ζ * ξ : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((star ((ζ : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *
        ((star ((ξ : ℂˣ) : ℂ)) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1
    push_cast
    rw [star_mul', mul_pow, mul_comm]
  · change (((ζ * ξ : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      ((((ζ : ℂˣ) : ℂ)) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((((ξ : ℂˣ) : ℂ)) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1
    push_cast
    rw [mul_pow, mul_comm]
  · change (((ζ * ξ : rootsOfUnity 6 ℂ) : ℂˣ) : ℂ) = ((ζ : ℂˣ) : ℂ) * ((ξ : ℂˣ) : ℂ)
    push_cast
    rfl

/-- `ζ ↦ (ζ̄²·1, ζ³·1, ζ)` as a homomorphism. -/
def kerHom : rootsOfUnity 6 ℂ →* SU3 × SU2 × U1 where
  toFun := kerElt
  map_one' := kerElt_one
  map_mul' := kerElt_mul

theorem ker_eq_range : symHom.ker = kerHom.range := by
  ext x
  rw [MonoidHom.mem_ker, sym_ker, MonoidHom.mem_range]
  constructor
  · rintro ⟨ζ, rfl⟩; exact ⟨ζ, rfl⟩
  · rintro ⟨ζ, rfl⟩; exact ⟨ζ, rfl⟩

/-- **The kernel is the group of sixth roots of unity, `ℤ₆`.** -/
def kerEquiv : rootsOfUnity 6 ℂ ≃* symHom.ker :=
  (MonoidHom.ofInjective (f := kerHom) kerElt_injective).trans
    (MulEquiv.subgroupCongr ker_eq_range.symm)

/-- **The kernel has six elements and is cyclic: `ℤ₆`.** -/
theorem ker_card : Nat.card (rootsOfUnity 6 ℂ) = 6 := Complex.card_rootsOfUnity 6

theorem ker_cyclic : IsCyclic (rootsOfUnity 6 ℂ) := inferInstance

/-- **`(SU(3) × SU(2) × U(1)) ⧸ ker ≃* S(U(3) × U(2))`.** -/
def sym_quotient : (SU3 × SU2 × U1) ⧸ symHom.ker ≃* SU32 :=
  QuotientGroup.quotientKerEquivOfSurjective symHom sym_surjective

end

end Comparison.GroupsContinuumLaw
