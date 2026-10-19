module

public import Comparison.Existence.Walk

/-!
# Book IX. Matter: one generation seen from the plane (Proposition 45)

A plane `F = {h, k}` of the five directions and the
three lines `C` outside it. A two-spinor state `e_S` disagrees on the lines of `S` (`|S| = 0, 2, 4`); it meets
the plane in `N_F = |S ∩ F|` lines and the three outside lines in `N_C = |S ∩ C|`.

* `hyper`: `Y = N_F/2 − N_C/3`; `charge`: `Q = N_k − N_C/3`; `isospin`: `T₃ = (N_k − N_h)/2`.
  The integer forms `6Y = 3N_F − 2N_C`, `3Q`, `6T₃` are checked by `decide` and carried to `ℚ`.
* `generation_classes`: `(N_C, N_F) = (0,0), (1,1), (2,0), (0,2), (2,2), (3,1)` on `1, 6, 3, 1, 3, 2`
  two-spinor states: `(1,1)₀, (3,2)_{1/6}, (3̄,1)_{−2/3}, (1,1)₁, (3̄,1)_{1/3}, (1,2)_{−1/2}`;
  `hyper_values`: the hypercharges `0, 1/6, −2/3, 1, 1/3, −1/2` with these multiplicities.
* `no_anomaly`: `Σ Y = 0`, `Σ Y³ = 0`, `Σ_{N_C ∈ {1,2}} Y = 0`, `Σ_{N_F = 1} Y = 0`; as many states
  in triplets as in anti-triplets; eight states in doublets.
* `charge_eq`: `Q = T₃ + Y` on all sixteen; `charge_values`: `0` twice, `2/3, −1/3, −2/3, 1/3` three
  times each, `1` and `−1` once; `lastDirection_line_neutral`: `Q(ℓ_h) = 0`, `Q(ℓ_k) = −1`.
* `plane_meets`: the ten symmetric states meet `F` in a plane, in a line, or only in the singlet: `1, 6, 3`.

Every statement holds for each of the twenty ordered planes (last-step direction `h`, other line `k`).
-/

@[expose] public section

namespace Comparison

/-- The lines of the plane `{h, k}` on which the two-spinor state disagrees. -/
def nPlane (h k : Fin 5) (r : Fin 16) : ℕ := (disagreeSet r ∩ {h, k}).card

/-- The lines outside the plane on which the two-spinor state disagrees. -/
def nOut (h k : Fin 5) (r : Fin 16) : ℕ := (disagreeSet r \ {h, k}).card

/-- Six times the hypercharge: `6Y = 3N_F − 2N_C`. -/
def hyper6 (h k : Fin 5) (r : Fin 16) : ℤ := 3 * (nPlane h k r : ℤ) - 2 * (nOut h k r : ℤ)

/-- Three times the charge: `3Q = 3N_k − N_C`. -/
def charge3 (h k : Fin 5) (r : Fin 16) : ℤ :=
  3 * (if k ∈ disagreeSet r then 1 else 0) - (nOut h k r : ℤ)

/-- Six times the isospin: `6T₃ = 3(N_k − N_h)`. -/
def isospin6 (h k : Fin 5) (r : Fin 16) : ℤ :=
  3 * ((if k ∈ disagreeSet r then 1 else 0) - (if h ∈ disagreeSet r then 1 else 0))

/-- **The hypercharge** `Y = N_F/2 − N_C/3`. -/
def hyper (h k : Fin 5) (r : Fin 16) : ℚ := (nPlane h k r : ℚ) / 2 - (nOut h k r : ℚ) / 3

/-- **The charge** `Q = N_k − N_C/3`. -/
def charge (h k : Fin 5) (r : Fin 16) : ℚ :=
  (if k ∈ disagreeSet r then 1 else 0) - (nOut h k r : ℚ) / 3

/-- `T₃ = (N_k − N_h)/2`. -/
def isospin (h k : Fin 5) (r : Fin 16) : ℚ :=
  ((if k ∈ disagreeSet r then 1 else 0) - (if h ∈ disagreeSet r then 1 else 0)) / 2

theorem hyper_eq (h k : Fin 5) (r : Fin 16) : hyper h k r = (hyper6 h k r : ℚ) / 6 := by
  simp only [hyper, hyper6]
  push_cast
  ring

theorem charge_eq3 (h k : Fin 5) (r : Fin 16) : charge h k r = (charge3 h k r : ℚ) / 3 := by
  simp only [charge, charge3]
  push_cast
  split_ifs <;> ring

theorem isospin_eq (h k : Fin 5) (r : Fin 16) : isospin h k r = (isospin6 h k r : ℚ) / 6 := by
  simp only [isospin, isospin6]
  push_cast
  split_ifs <;> ring

/-- **One generation:** the sixteen two-spinor states by `(N_C, N_F)`: `1, 6, 3, 1, 3, 2`. -/
theorem generation_classes : ∀ h k : Fin 5, h ≠ k →
    (Finset.univ.filter fun r => nOut h k r = 0 ∧ nPlane h k r = 0).card = 1 ∧
    (Finset.univ.filter fun r => nOut h k r = 1 ∧ nPlane h k r = 1).card = 6 ∧
    (Finset.univ.filter fun r => nOut h k r = 2 ∧ nPlane h k r = 0).card = 3 ∧
    (Finset.univ.filter fun r => nOut h k r = 0 ∧ nPlane h k r = 2).card = 1 ∧
    (Finset.univ.filter fun r => nOut h k r = 2 ∧ nPlane h k r = 2).card = 3 ∧
    (Finset.univ.filter fun r => nOut h k r = 3 ∧ nPlane h k r = 1).card = 2 := by
  decide +kernel

theorem hyper6_values : ∀ h k : Fin 5, h ≠ k →
    (Finset.univ.filter fun r => hyper6 h k r = 0).card = 1 ∧
    (Finset.univ.filter fun r => hyper6 h k r = 1).card = 6 ∧
    (Finset.univ.filter fun r => hyper6 h k r = -4).card = 3 ∧
    (Finset.univ.filter fun r => hyper6 h k r = 6).card = 1 ∧
    (Finset.univ.filter fun r => hyper6 h k r = 2).card = 3 ∧
    (Finset.univ.filter fun r => hyper6 h k r = -3).card = 2 := by
  decide +kernel

theorem hyper_eq_iff (h k : Fin 5) (r : Fin 16) (y : ℤ) :
    hyper h k r = (y : ℚ) / 6 ↔ hyper6 h k r = y := by
  rw [hyper_eq]
  constructor
  · intro e
    have : (hyper6 h k r : ℚ) = y := by linarith
    exact_mod_cast this
  · intro e
    rw [e]

/-- **The hypercharges of one generation:** `0, 1/6, −2/3, 1, 1/3, −1/2` on `1, 6, 3, 1, 3, 2`. -/
theorem hyper_values (h k : Fin 5) (hk : h ≠ k) :
    (Finset.univ.filter fun r => hyper h k r = 0).card = 1 ∧
    (Finset.univ.filter fun r => hyper h k r = 1 / 6).card = 6 ∧
    (Finset.univ.filter fun r => hyper h k r = -2 / 3).card = 3 ∧
    (Finset.univ.filter fun r => hyper h k r = 1).card = 1 ∧
    (Finset.univ.filter fun r => hyper h k r = 1 / 3).card = 3 ∧
    (Finset.univ.filter fun r => hyper h k r = -1 / 2).card = 2 := by
  have e : ∀ (q : ℚ) (y : ℤ), q = (y : ℚ) / 6 →
      (Finset.univ.filter fun r => hyper h k r = q) =
        Finset.univ.filter fun r => hyper6 h k r = y := by
    intro q y hq
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq, hyper_eq_iff]
  have v := hyper6_values h k hk
  rw [e 0 0 (by norm_num), e (1 / 6) 1 (by norm_num), e (-2 / 3) (-4) (by norm_num),
    e 1 6 (by norm_num), e (1 / 3) 2 (by norm_num), e (-1 / 2) (-3) (by norm_num)]
  exact v

theorem hyper6_sums : ∀ h k : Fin 5, h ≠ k →
    ∑ r, hyper6 h k r = 0 ∧ ∑ r, hyper6 h k r ^ 3 = 0 ∧
    ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper6 h k r = 0 ∧
    ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper6 h k r = 0 ∧
    (Finset.univ.filter fun r => nOut h k r = 1).card =
      (Finset.univ.filter fun r => nOut h k r = 2).card ∧
    (Finset.univ.filter fun r => nPlane h k r = 1).card = 8 := by
  decide +kernel

/-- **No anomaly:** `Σ Y = Σ Y³ = 0`, the mixed sums with colour and with the plane vanish, as many
states sit in triplets as in anti-triplets, and eight states sit in doublets. -/
theorem no_anomaly (h k : Fin 5) (hk : h ≠ k) :
    ∑ r, hyper h k r = 0 ∧ ∑ r, hyper h k r ^ 3 = 0 ∧
    ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper h k r = 0 ∧
    ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper h k r = 0 ∧
    (Finset.univ.filter fun r => nOut h k r = 1).card =
      (Finset.univ.filter fun r => nOut h k r = 2).card ∧
    (Finset.univ.filter fun r => nPlane h k r = 1).card = 8 := by
  obtain ⟨s1, s3, sc, sf, t, d⟩ := hyper6_sums h k hk
  simp only [hyper_eq, div_pow, ← Finset.sum_div]
  refine ⟨?_, ?_, ?_, ?_, t, d⟩
  · rw [← Int.cast_sum, s1]; simp
  · simp only [← Int.cast_pow, ← Int.cast_sum, s3]; simp
  · rw [← Int.cast_sum, sc]; simp
  · rw [← Int.cast_sum, sf]; simp

theorem charge_eq6 : ∀ h k : Fin 5, h ≠ k → ∀ r, 2 * charge3 h k r = isospin6 h k r + hyper6 h k r := by
  decide +kernel

/-- **`Q = T₃ + Y`** on all sixteen two-spinor states. -/
theorem charge_eq (h k : Fin 5) (hk : h ≠ k) (r : Fin 16) :
    charge h k r = isospin h k r + hyper h k r := by
  rw [charge_eq3, isospin_eq, hyper_eq]
  have := charge_eq6 h k hk r
  have h' : (2 * charge3 h k r : ℚ) = isospin6 h k r + hyper6 h k r := by exact_mod_cast this
  linarith

theorem charge3_values : ∀ h k : Fin 5, h ≠ k →
    (Finset.univ.filter fun r => charge3 h k r = 0).card = 2 ∧
    (Finset.univ.filter fun r => charge3 h k r = 2).card = 3 ∧
    (Finset.univ.filter fun r => charge3 h k r = -1).card = 3 ∧
    (Finset.univ.filter fun r => charge3 h k r = -2).card = 3 ∧
    (Finset.univ.filter fun r => charge3 h k r = 1).card = 3 ∧
    (Finset.univ.filter fun r => charge3 h k r = 3).card = 1 ∧
    (Finset.univ.filter fun r => charge3 h k r = -3).card = 1 := by
  decide +kernel

theorem charge_eq_iff (h k : Fin 5) (r : Fin 16) (y : ℤ) :
    charge h k r = (y : ℚ) / 3 ↔ charge3 h k r = y := by
  rw [charge_eq3]
  constructor
  · intro e
    have : (charge3 h k r : ℚ) = y := by linarith
    exact_mod_cast this
  · intro e
    rw [e]

/-- **The charges of one generation:** `0` twice, `2/3, −1/3, −2/3, 1/3` three times each, `1` and
`−1` once. -/
theorem charge_values (h k : Fin 5) (hk : h ≠ k) :
    (Finset.univ.filter fun r => charge h k r = 0).card = 2 ∧
    (Finset.univ.filter fun r => charge h k r = 2 / 3).card = 3 ∧
    (Finset.univ.filter fun r => charge h k r = -1 / 3).card = 3 ∧
    (Finset.univ.filter fun r => charge h k r = -2 / 3).card = 3 ∧
    (Finset.univ.filter fun r => charge h k r = 1 / 3).card = 3 ∧
    (Finset.univ.filter fun r => charge h k r = 1).card = 1 ∧
    (Finset.univ.filter fun r => charge h k r = -1).card = 1 := by
  have e : ∀ (q : ℚ) (y : ℤ), q = (y : ℚ) / 3 →
      (Finset.univ.filter fun r => charge h k r = q) =
        Finset.univ.filter fun r => charge3 h k r = y := by
    intro q y hq
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq, charge_eq_iff]
  have v := charge3_values h k hk
  rw [e 0 0 (by norm_num), e (2 / 3) 2 (by norm_num), e (-1 / 3) (-1) (by norm_num),
    e (-2 / 3) (-2) (by norm_num), e (1 / 3) 1 (by norm_num), e 1 3 (by norm_num),
    e (-1) (-3) (by norm_num)]
  exact v

/-- **The last-step direction is neutral:** the vector state of the last-step direction, `ℓ_h = e_{T_h}`, has `Q = 0`; that of
the plane's other line has `Q = −1`. -/
theorem lastDirection_line_neutral (h k : Fin 5) (hk : h ≠ k) :
    charge h k (transition h 0) = 0 ∧ charge h k (transition k 0) = -1 := by
  have : ∀ h k : Fin 5, h ≠ k → charge3 h k (transition h 0) = 0 ∧ charge3 h k (transition k 0) = -3 := by
    decide +kernel
  obtain ⟨a, b⟩ := this h k hk
  rw [charge_eq3, charge_eq3, a, b]
  norm_num

/-- **The ten symmetric states meet the plane `F` in a plane, in a line, or only in the singlet: `1, 6, 3`.** -/
theorem plane_meets : ∀ h k : Fin 5, h ≠ k →
    (Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 2).card = 1 ∧
    (Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 1).card = 6 ∧
    (Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 0).card = 3 := by
  decide +kernel

end Comparison

end
