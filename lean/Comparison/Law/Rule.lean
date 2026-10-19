module

public import Comparison.Law.Carried

/-!
# The law, II: the one rule at every divided set (Proposition 108)

A piece of a constant lives on a divided set `S ⊆ {n, h, k, c₁, c₂, c₃}` (`Fin 6`, `n = 0`), with
`k = linesIn S` lines. The one rule:
`z_S = i^{|S|}`, `L_S = (5 − k) + k z_S²`, `w_S = z_S/L_S`, `u_S = z_S/4`, power `1` on even and
`1/2` on odd divided sets; with `P = z_S²`: `Φ = −1/(16 + 3P)`, the reflection `e_S = 1 − 2|w_S|`, the
transmission `t_S = 2|w_S|`, `Ψ(w_S²)`, `N(S)`.

* `zS_eq_whole`: **`z_S` is the whole described once at `S`**, the diagonal entry of `Λ(iI) = i^N`.
* `LS_carried`: **`L_S = 5 − (5/2)(1 − z_S²)(1 + det Σ₆[S, S])`**, the transported matrix's principal
  minor; `LS_odd`: at an odd divided set `L_S = −5 det Σ₆[S, S] = 5(−1)^k det σ[S ∩ lines]`;
  `LS_even`: at an even divided set `L_S = 5`.
* `PhiS_eq`: `Φ(z_S) = −1/(16 + 3P)`; `powS_eq`: power `(3 + P)/4`; `uS_sq`: `u_S² = P/16`.
* `PsiS_eq`: `Ψ(w_S²) = P/(L_S² + 3P)` at every divided set; `PsiS_plane`: `= 1/(15 + 13P)` exactly
  when `P = 1` or `k ∈ {2, 3}` (the two signs of a plane and every even divided set); at `{n}` and
  `{t}` the rule gives `−1/22` and `−1/6`.
* `norm_wS`: `|w_S| = 1/|L_S|`; `eS_four`: `e_S = 1 − 2/(4 + P)` exactly when `P = 1` or
  `k ∈ {1, 4}` (`|L_S| = 4 + P`): Proposition 108's statement for a divided set of one line or of none holds at the
  even divided sets and the odd divided sets with one line, and also at the odd divided sets with four.
* `NS_turns`: `N(S) − [|S| odd]` is the number of rotations of the six with one end in `S`.
* `twin_lines`, `twin_sign`: moving the singlet in or out keeps the lines and exchanges count and
  amplitude.
* `table_*`: the rule's values at the twelve divided sets of Proposition 108's table.
-/

@[expose] public section

namespace Comparison

open Matrix Complex

namespace Law

/-! ## The rule -/

/-- **The phase of a divided set:** `z_S = i^{|S|}`. -/
noncomputable def zS (S : Finset (Fin 6)) : ℂ := I ^ S.card

/-- The sign of a divided set, `P_S = (−1)^{|S|}`: `+1` counts, `−1` amplitudes. -/
def signS (S : Finset (Fin 6)) : ℤ := (-1) ^ S.card

/-- The comparison the divided set reads, as an integer: `(5 − k) + k P_S`. -/
def LZ (S : Finset (Fin 6)) : ℤ := 5 - (linesIn S : ℤ) + (linesIn S : ℤ) * signS S

/-- **`L_S = (5 − k) + k z_S²`.** -/
noncomputable def LS (S : Finset (Fin 6)) : ℂ := (5 - (linesIn S : ℂ)) + (linesIn S : ℂ) * zS S ^ 2

/-- **`w_S = z_S/L_S`.** -/
noncomputable def wS (S : Finset (Fin 6)) : ℂ := zS S / LS S

/-- **`u_S = z_S/4`.** -/
noncomputable def uS (S : Finset (Fin 6)) : ℂ := zS S / 4

/-- **The power:** `1` on an even divided set (a count), `1/2` on an odd one (an amplitude). -/
noncomputable def powS (S : Finset (Fin 6)) : ℝ := if Even S.card then 1 else 1 / 2

/-- The signed excursion `Φ(z) = −z⁴/(16 + 3z²)` (Proposition 30). -/
noncomputable def Phi (z : ℂ) : ℂ := -z ^ 4 / (16 + 3 * z ^ 2)

/-- **`Φ(z_S)`**, the signed first return at the divided set. -/
noncomputable def PhiS (S : Finset (Fin 6)) : ℂ := Phi (zS S)

/-- The association `Ψ(v) = v/(1 + 3v)` (Proposition 49). -/
noncomputable def Psi (v : ℂ) : ℂ := v / (1 + 3 * v)

/-- **`Ψ(w_S²)`.** -/
noncomputable def PsiS (S : Finset (Fin 6)) : ℂ := Psi (wS S ^ 2)

/-- **The reflection** `e_S = 1 − 2|w_S|`. -/
noncomputable def eS (S : Finset (Fin 6)) : ℝ := 1 - 2 * ‖wS S‖

/-- **The transmission** `t_S = 2|w_S|`. -/
noncomputable def tS (S : Finset (Fin 6)) : ℝ := 2 * ‖wS S‖

/-- **`N(S)`:** the rotations of the six with one end in `S`, and one more when `|S|` is odd. -/
def NS (S : Finset (Fin 6)) : ℕ := S.card * (6 - S.card) + if Odd S.card then 1 else 0

/-- The counterpart of a divided set: the singlet moved in or out. -/
def twin (S : Finset (Fin 6)) : Finset (Fin 6) := symmDiff S {0}

/-! ## The phase and the sign -/

theorem I_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem zS_sq (S : Finset (Fin 6)) : zS S ^ 2 = (signS S : ℂ) := by
  rw [zS, signS, ← pow_mul, mul_comm, pow_mul, Complex.I_sq]
  push_cast
  ring

theorem zS_pow_four (S : Finset (Fin 6)) : zS S ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, zS_sq, signS]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem signS_sq (S : Finset (Fin 6)) : signS S ^ 2 = 1 := by
  rw [signS, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem signS_cases (S : Finset (Fin 6)) : signS S = 1 ∨ signS S = -1 := by
  rw [signS]
  rcases Nat.even_or_odd S.card with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem signS_even {S : Finset (Fin 6)} (h : Even S.card) : signS S = 1 := h.neg_one_pow

theorem signS_odd {S : Finset (Fin 6)} (h : Odd S.card) : signS S = -1 := h.neg_one_pow

/-- **`z_S` is the whole described once at `S`:** the diagonal entry of `Λ(iI) = i^N`. -/
theorem zS_eq_whole (S : Finset (Fin 6)) :
    zS S = extPow (I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) S S := by
  rw [extPow_smul_one, gradePow, Matrix.diagonal_apply_eq, zS]

/-- `Λ(iΣ₆)_{SS} = z_S det Σ₆[S, S]`. -/
theorem whole_carried_diag (S : Finset (Fin 6)) :
    extPow (I • carriedC) S S = zS S * minor carriedC S S := by
  rw [extPow_smul]
  simp only [gradePow, Matrix.diagonal_mul, extPow, Matrix.of_apply, zS]

/-! ## `L_S` and the transported matrix -/

theorem LS_eq_LZ (S : Finset (Fin 6)) : LS S = (LZ S : ℂ) := by
  rw [LS, LZ, zS_sq]
  push_cast
  ring

theorem linesIn_le (S : Finset (Fin 6)) : linesIn S ≤ 5 := by
  revert S
  decide

/-- `det Σ₆[S, S] = P_S (1 − 2k/5)` over `ℂ`. -/
theorem minor_carriedC_self (S : Finset (Fin 6)) :
    minor carriedC S S = (signS S : ℂ) * (1 - 2 / 5 * (linesIn S : ℂ)) := by
  rw [minor_carried_self, signS]
  push_cast
  ring

/-- **`L_S` from the transported matrix:** `L_S = 5 − (5/2)(1 − z_S²)(1 + det Σ₆[S, S])`. -/
theorem LS_carried (S : Finset (Fin 6)) :
    LS S = 5 - 5 / 2 * (1 - zS S ^ 2) * (1 + minor carriedC S S) := by
  rw [minor_carriedC_self, LS, zS_sq]
  rcases signS_cases S with h | h <;> rw [h] <;> push_cast <;> ring

/-- **At an odd divided set** `L_S = −5 det Σ₆[S, S]`. -/
theorem LS_odd {S : Finset (Fin 6)} (h : Odd S.card) : LS S = -5 * minor carriedC S S := by
  rw [minor_carriedC_self, LS, zS_sq, signS_odd h]
  push_cast
  ring

/-- **At an even divided set** `L_S = 5`. -/
theorem LS_even {S : Finset (Fin 6)} (h : Even S.card) : LS S = 5 := by
  rw [LS, zS_sq, signS_even h]
  push_cast
  ring

/-- **At an odd divided set** `L_S = 5(−1)^k det σ[S ∩ lines, S ∩ lines]`, the coin's minor. -/
theorem LS_odd_coin {S : Finset (Fin 6)} (h : Odd S.card) :
    LS S = 5 * (-1) ^ linesIn S * ((minor coin (linesOf S) (linesOf S) : ℚ) : ℂ) := by
  rw [minor_coin_self, card_linesOf, LS, zS_sq, signS_odd h]
  push_cast
  have h1 : ((-1 : ℂ) ^ linesIn S) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  linear_combination (-(5 - 2 * (linesIn S : ℂ))) * h1

/-- `L_S` is never zero. -/
theorem LZ_ne_zero (S : Finset (Fin 6)) : LZ S ≠ 0 := by
  revert S
  decide

theorem LS_ne_zero (S : Finset (Fin 6)) : LS S ≠ 0 := by
  rw [LS_eq_LZ]
  exact_mod_cast LZ_ne_zero S

/-! ## The numbers the rule gives -/

/-- **`Φ(z_S) = −1/(16 + 3P)`.** -/
theorem PhiS_eq (S : Finset (Fin 6)) : PhiS S = -1 / (16 + 3 * (signS S : ℂ)) := by
  rw [PhiS, Phi, zS_pow_four, zS_sq]

/-- `Φ = −1/19` on an even divided set, `−1/13` on an odd one. -/
theorem PhiS_values (S : Finset (Fin 6)) :
    (Even S.card → PhiS S = -1 / 19) ∧ (Odd S.card → PhiS S = -1 / 13) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [PhiS_eq, signS_even h]
    norm_num
  · rw [PhiS_eq, signS_odd h]
    norm_num

/-- **The power is `(3 + P)/4`.** -/
theorem powS_eq (S : Finset (Fin 6)) : powS S = (3 + (signS S : ℝ)) / 4 := by
  rw [powS]
  rcases Nat.even_or_odd S.card with h | h
  · simp only [h, ↓reduceIte, signS_even h]
    norm_num
  · have h' : ¬ Even S.card := Nat.not_even_iff_odd.mpr h
    simp only [h', ↓reduceIte, signS_odd h]
    norm_num

/-- **`u_S² = P/16`.** -/
theorem uS_sq (S : Finset (Fin 6)) : uS S ^ 2 = (signS S : ℂ) / 16 := by
  rw [uS, div_pow, zS_sq]
  norm_num

/-- `w_S² = P/L_S²`. -/
theorem wS_sq (S : Finset (Fin 6)) : wS S ^ 2 = (signS S : ℂ) / LS S ^ 2 := by
  rw [wS, div_pow, zS_sq]

theorem LZ_sq_add_ne (S : Finset (Fin 6)) : LZ S ^ 2 + 3 * signS S ≠ 0 := by
  revert S
  decide

/-- The integer form of the association's values. -/
theorem psi_int (S : Finset (Fin 6)) :
    (signS S * (15 + 13 * signS S) = LZ S ^ 2 + 3 * signS S ↔
      (Even S.card ∨ linesIn S = 2 ∨ linesIn S = 3)) ∧
    (Odd S.card → (linesIn S = 0 ∨ linesIn S = 5) → signS S * 22 = -(LZ S ^ 2 + 3 * signS S)) ∧
    (Odd S.card → (linesIn S = 1 ∨ linesIn S = 4) → signS S * 6 = -(LZ S ^ 2 + 3 * signS S)) := by
  revert S
  decide

/-- **`Ψ(w_S²) = P/(L_S² + 3P)`** at every divided set. -/
theorem PsiS_eq (S : Finset (Fin 6)) :
    PsiS S = (signS S : ℂ) / (LS S ^ 2 + 3 * (signS S : ℂ)) := by
  have hL := LS_ne_zero S
  rw [PsiS, Psi, wS_sq]
  have hden : LS S ^ 2 + 3 * (signS S : ℂ) ≠ 0 := by
    rw [LS_eq_LZ]
    exact_mod_cast LZ_sq_add_ne S
  field_simp

/-- **`Ψ(w_S²) = 1/(15 + 13P)` exactly at the even divided sets and at the odd divided sets with two or
three lines** (the two signs of a plane); elsewhere the rule gives `−1/22` (`k = 0, 5`) or `−1/6`
(`k = 1, 4`). -/
theorem PsiS_plane (S : Finset (Fin 6)) :
    (PsiS S = 1 / (15 + 13 * (signS S : ℂ)) ↔
      (Even S.card ∨ linesIn S = 2 ∨ linesIn S = 3)) ∧
    (Odd S.card → (linesIn S = 0 ∨ linesIn S = 5) → PsiS S = -1 / 22) ∧
    (Odd S.card → (linesIn S = 1 ∨ linesIn S = 4) → PsiS S = -1 / 6) := by
  obtain ⟨k1, k2, k3⟩ := psi_int S
  have hD : ((LZ S : ℂ) ^ 2 + 3 * (signS S : ℂ)) ≠ 0 := by exact_mod_cast LZ_sq_add_ne S
  have hE : (15 + 13 * (signS S : ℂ)) ≠ 0 := by
    rcases signS_cases S with h | h <;> rw [h] <;> norm_num
  rw [PsiS_eq, LS_eq_LZ]
  refine ⟨?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [div_eq_div_iff hD hE, one_mul, ← k1]
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  · rw [div_eq_div_iff hD (by norm_num)]
    have := k2 h1 h2
    have h' : ((signS S * 22 : ℤ) : ℂ) = ((-(LZ S ^ 2 + 3 * signS S) : ℤ) : ℂ) := by rw [this]
    push_cast at h'
    linear_combination h'
  · rw [div_eq_div_iff hD (by norm_num)]
    have := k3 h1 h2
    have h' : ((signS S * 6 : ℤ) : ℂ) = ((-(LZ S ^ 2 + 3 * signS S) : ℤ) : ℂ) := by rw [this]
    push_cast at h'
    linear_combination h'

/-- `|w_S| = 1/|L_S|`. -/
theorem norm_wS (S : Finset (Fin 6)) : ‖wS S‖ = 1 / |(LZ S : ℝ)| := by
  rw [wS, norm_div, LS_eq_LZ, zS, norm_pow, Complex.norm_I, one_pow]
  congr 1
  rw [Complex.norm_intCast]

/-- The reflection and the transmission add to one. -/
theorem eS_add_tS (S : Finset (Fin 6)) : eS S + tS S = 1 := by
  rw [eS, tS]
  ring

/-- **`e_S = 1 − 2/(4 + P)` exactly when `P = 1` or the divided set holds one line or four**
(`|L_S| = 4 + P`; at an odd divided set with four lines `L_S = −3`). -/
theorem eS_four (S : Finset (Fin 6)) :
    (eS S = 1 - 2 / (4 + (signS S : ℝ)) ↔
      (signS S = 1 ∨ linesIn S = 1 ∨ linesIn S = 4)) := by
  have key : ∀ S : Finset (Fin 6),
      (|LZ S| = 4 + signS S ↔ (signS S = 1 ∨ linesIn S = 1 ∨ linesIn S = 4)) := by
    decide
  have hL : (|(LZ S : ℝ)|) ≠ 0 := by
    rw [abs_ne_zero]
    exact_mod_cast LZ_ne_zero S
  have h4 : (4 + (signS S : ℝ)) ≠ 0 := by
    rcases signS_cases S with h | h <;> rw [h] <;> norm_num
  rw [eS, norm_wS, mul_one_div, ← key S]
  constructor
  · intro h
    have h2 : 2 / |(LZ S : ℝ)| = 2 / (4 + (signS S : ℝ)) := by linarith
    rw [div_eq_div_iff hL h4] at h2
    have h3 : |(LZ S : ℝ)| = 4 + (signS S : ℝ) := by linarith
    have h5 : ((|LZ S| : ℤ) : ℝ) = ((4 + signS S : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast h5
  · intro h
    have h5 : ((|LZ S| : ℤ) : ℝ) = ((4 + signS S : ℤ) : ℝ) := by rw [h]
    push_cast at h5
    rw [h5]

/-- **`N(S) − [|S| odd]` counts the rotations of the six with one end in `S`.** -/
theorem NS_turns (S : Finset (Fin 6)) :
    ((Finset.univ.powersetCard 2).filter fun p : Finset (Fin 6) => (p ∩ S).card = 1).card +
      (if Odd S.card then 1 else 0) = NS S := by
  revert S
  decide

/-! ## The counterpart -/

/-- **Moving the singlet in or out keeps the lines.** -/
theorem twin_lines (S : Finset (Fin 6)) : linesIn (twin S) = linesIn S := by
  revert S
  decide

/-- **… and exchanges count and amplitude.** -/
theorem twin_sign (S : Finset (Fin 6)) : signS (twin S) = -signS S := by
  revert S
  decide

theorem twin_twin (S : Finset (Fin 6)) : twin (twin S) = S := by
  revert S
  decide

/-! ## The twelve divided sets of Proposition 108 -/

/-- Here `{}`. -/
def sHere : Finset (Fin 6) := ∅
/-- The singlet `{n}`. -/
def sSinglet : Finset (Fin 6) := {0}
/-- A line with the singlet `{t, n}` (`t = k`). -/
def sLineSinglet : Finset (Fin 6) := {0, 2}
/-- A line alone `{t}` (`t = k`). -/
def sLine : Finset (Fin 6) := {2}
/-- The last-step direction with the singlet `{h, n}`. -/
def sLastDirectionSinglet : Finset (Fin 6) := {0, 1}
/-- The last-step direction alone `{h}`. -/
def sLastDirection : Finset (Fin 6) := {1}
/-- A plane `{a, b}` (`= {c₁, c₂}`). -/
def sPlane : Finset (Fin 6) := {3, 4}
/-- The plane with the singlet `{a, b, n}`. -/
def sPlaneSinglet : Finset (Fin 6) := {0, 3, 4}
/-- The plane `F = {h, k}`. -/
def sF : Finset (Fin 6) := {1, 2}
/-- The three lines outside `F`, `C = {c₁, c₂, c₃}`. -/
def sC : Finset (Fin 6) := {3, 4, 5}
/-- The counterpart of `C`, `C + {n}`. -/
def sCn : Finset (Fin 6) := {0, 3, 4, 5}
/-- The counterpart of `F`, `F + {n}`. -/
def sFn : Finset (Fin 6) := {0, 1, 2}

theorem card_lines_dividedSets :
    (sHere.card, linesIn sHere) = (0, 0) ∧ (sSinglet.card, linesIn sSinglet) = (1, 0) ∧
    (sLineSinglet.card, linesIn sLineSinglet) = (2, 1) ∧ (sLine.card, linesIn sLine) = (1, 1) ∧
    (sLastDirectionSinglet.card, linesIn sLastDirectionSinglet) = (2, 1) ∧ (sLastDirection.card, linesIn sLastDirection) = (1, 1) ∧
    (sPlane.card, linesIn sPlane) = (2, 2) ∧ (sPlaneSinglet.card, linesIn sPlaneSinglet) = (3, 2) ∧
    (sF.card, linesIn sF) = (2, 2) ∧ (sC.card, linesIn sC) = (3, 3) ∧
    (sCn.card, linesIn sCn) = (4, 3) ∧ (sFn.card, linesIn sFn) = (3, 2) := by
  decide

theorem twins_of_table :
    twin sHere = sSinglet ∧ twin sLine = sLineSinglet ∧ twin sLastDirection = sLastDirectionSinglet ∧ twin sPlane = sPlaneSinglet ∧
      twin sC = sCn ∧ twin sF = sFn := by
  decide

/-- The rule's numbers from `(|S|, k)` alone. -/
theorem rule_of (S : Finset (Fin 6)) (c k : ℕ) (hc : S.card = c) (hk : linesIn S = k) :
    zS S = I ^ c ∧ LS S = (5 - (k : ℂ)) + (k : ℂ) * (I ^ c) ^ 2 := by
  refine ⟨by rw [zS, hc], by rw [LS, zS, hc, hk]⟩


/-- The rule's numbers at a divided set with `|S| = c`, `L_S = L` and `P_S = P`. -/
theorem rule_values (S : Finset (Fin 6)) (c : ℕ) (L P : ℤ) (hc : S.card = c) (hL : LZ S = L)
    (hP : signS S = P) :
    zS S = I ^ c ∧ LS S = L ∧ wS S = I ^ c / L ∧ uS S = I ^ c / 4 ∧
      eS S = 1 - 2 / |(L : ℝ)| ∧ tS S = 2 / |(L : ℝ)| ∧ PhiS S = -1 / (16 + 3 * (P : ℂ)) ∧
      PsiS S = (P : ℂ) / ((L : ℂ) ^ 2 + 3 * (P : ℂ)) := by
  have hz : zS S = I ^ c := by rw [zS, hc]
  have hLS : LS S = L := by rw [LS_eq_LZ, hL]
  refine ⟨hz, hLS, by rw [wS, hz, hLS], by rw [uS, hz], ?_, ?_, ?_, ?_⟩
  · rw [eS, norm_wS, hL]
    ring
  · rw [tS, norm_wS, hL]
    ring
  · rw [PhiS_eq, hP]
  · rw [PsiS_eq, hP, LS_eq_LZ, hL]

/-- **Here `{}`** (0|6): `z = 1`, `L = 5`, `w = 1/5`, `u = 1/4`, power 1, `e = 3/5`, `t = 2/5`,
`Φ = −1/19`, `Ψ = 1/28`, `N = 0`. -/
theorem table_here :
    zS sHere = 1 ∧ LS sHere = 5 ∧ wS sHere = 1 / 5 ∧ uS sHere = 1 / 4 ∧ powS sHere = 1 ∧
      eS sHere = 3 / 5 ∧ tS sHere = 2 / 5 ∧ PhiS sHere = -1 / 19 ∧ PsiS sHere = 1 / 28 ∧
      NS sHere = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values sHere 0 5 1 (by decide) (by decide) (by decide)
  have hp : powS sHere = 1 := by rw [powS_eq, show signS sHere = 1 by decide]; norm_num
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num,
    hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num, by rw [h8]; norm_num,
    by decide⟩

/-- **The singlet `{n}`** (1|5): `z = i`, `L = 5`, `w = i/5`, `u = i/4`, power 1/2, `e = 3/5`,
`t = 2/5`, `Φ = −1/13`, `Ψ = −1/22`, `N = 6`. -/
theorem table_singlet :
    zS sSinglet = I ∧ LS sSinglet = 5 ∧ wS sSinglet = I / 5 ∧ uS sSinglet = I / 4 ∧ powS sSinglet = 1 / 2 ∧
      eS sSinglet = 3 / 5 ∧ tS sSinglet = 2 / 5 ∧ PhiS sSinglet = -1 / 13 ∧ PsiS sSinglet = -1 / 22 ∧
      NS sSinglet = 6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values sSinglet 1 5 (-1) (by decide) (by decide)
    (by decide)
  have hp : powS sSinglet = 1 / 2 := by rw [powS_eq, show signS sSinglet = -1 by decide]; norm_num
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num,
    hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num, by rw [h8]; norm_num,
    by decide⟩

/-- **A line with the singlet `{t, n}`** and **the last-step direction with the singlet `{h, n}`** (2|4): `z = −1`,
`L = 5`, `w = −1/5`, `u = −1/4`, power 1, `e = 3/5`, `t = 2/5`, `Φ = −1/19`, `Ψ = 1/28`, `N = 8`. -/
theorem table_lineSinglet (S : Finset (Fin 6)) (hS : S = sLineSinglet ∨ S = sLastDirectionSinglet ∨ S = sPlane ∨
    S = sF) :
    zS S = -1 ∧ LS S = 5 ∧ wS S = -1 / 5 ∧ uS S = -1 / 4 ∧ powS S = 1 ∧
      eS S = 3 / 5 ∧ tS S = 2 / 5 ∧ PhiS S = -1 / 19 ∧ PsiS S = 1 / 28 ∧ NS S = 8 := by
  have hc : S.card = 2 := by rcases hS with h | h | h | h <;> rw [h] <;> decide
  have hL : LZ S = 5 := by rcases hS with h | h | h | h <;> rw [h] <;> decide
  have hP : signS S = 1 := by rcases hS with h | h | h | h <;> rw [h] <;> decide
  have hN : NS S = 8 := by rcases hS with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values S 2 5 1 hc hL hP
  have hp : powS S = 1 := by rw [powS_eq, hP]; norm_num
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num,
    hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num, by rw [h8]; norm_num,
    hN⟩

/-- **A line alone `{t}`** and **the last-step direction alone `{h}`** (1|5): `z = i`, `L = 3`, `w = i/3`,
`u = i/4`, power 1/2, `e = 1/3`, `t = 2/3`, `Φ = −1/13`, `Ψ = −1/6`, `N = 6`. -/
theorem table_line (S : Finset (Fin 6)) (hS : S = sLine ∨ S = sLastDirection) :
    zS S = I ∧ LS S = 3 ∧ wS S = I / 3 ∧ uS S = I / 4 ∧ powS S = 1 / 2 ∧
      eS S = 1 / 3 ∧ tS S = 2 / 3 ∧ PhiS S = -1 / 13 ∧ PsiS S = -1 / 6 ∧ NS S = 6 := by
  have hc : S.card = 1 := by rcases hS with h | h <;> rw [h] <;> decide
  have hL : LZ S = 3 := by rcases hS with h | h <;> rw [h] <;> decide
  have hP : signS S = -1 := by rcases hS with h | h <;> rw [h] <;> decide
  have hN : NS S = 6 := by rcases hS with h | h <;> rw [h] <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values S 1 3 (-1) hc hL hP
  have hp : powS S = 1 / 2 := by rw [powS_eq, hP]; norm_num
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num,
    hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num, by rw [h8]; norm_num,
    hN⟩

/-- **The plane with the singlet `{a, b, n}`** and **`F + {n}`** (3|3): `z = −i`, `L = 1`, `w = −i`,
`u = −i/4`, power 1/2, `e = −1`, `t = 2`, `Φ = −1/13`, `Ψ = 1/2`, `N = 10`. -/
theorem table_planeSinglet (S : Finset (Fin 6)) (hS : S = sPlaneSinglet ∨ S = sFn) :
    zS S = -I ∧ LS S = 1 ∧ wS S = -I ∧ uS S = -I / 4 ∧ powS S = 1 / 2 ∧
      eS S = -1 ∧ tS S = 2 ∧ PhiS S = -1 / 13 ∧ PsiS S = 1 / 2 ∧ NS S = 10 := by
  have hc : S.card = 3 := by rcases hS with h | h <;> rw [h] <;> decide
  have hL : LZ S = 1 := by rcases hS with h | h <;> rw [h] <;> decide
  have hP : signS S = -1 := by rcases hS with h | h <;> rw [h] <;> decide
  have hN : NS S = 10 := by rcases hS with h | h <;> rw [h] <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values S 3 1 (-1) hc hL hP
  have hp : powS S = 1 / 2 := by rw [powS_eq, hP]; norm_num
  have hI3 : I ^ 3 = -I := Complex.I_pow_three
  refine ⟨by rw [h1, hI3], by rw [h2]; norm_num, by rw [h3, hI3]; norm_num,
    by rw [h4, hI3], hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num,
    by rw [h8]; norm_num, hN⟩

/-- **The three lines outside the plane `hk`, `C`** (3|3): `z = −i`, `L = −1`, `w = i`,
`u = −i/4`, power 1/2, `e = −1`, `t = 2`, `Φ = −1/13`, `Ψ = 1/2`, `N = 10`. -/
theorem table_C :
    zS sC = -I ∧ LS sC = -1 ∧ wS sC = I ∧ uS sC = -I / 4 ∧ powS sC = 1 / 2 ∧
      eS sC = -1 ∧ tS sC = 2 ∧ PhiS sC = -1 / 13 ∧ PsiS sC = 1 / 2 ∧ NS sC = 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values sC 3 (-1) (-1) (by decide) (by decide)
    (by decide)
  have hp : powS sC = 1 / 2 := by rw [powS_eq, show signS sC = -1 by decide]; norm_num
  have hI3 : I ^ 3 = -I := Complex.I_pow_three
  refine ⟨by rw [h1, hI3], by rw [h2]; norm_num, by rw [h3, hI3]; norm_num,
    by rw [h4, hI3], hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num,
    by rw [h8]; norm_num, by decide⟩

/-- **The counterpart of `C`, `C + {n}`** (as a division `F`, 2|4): `z = 1`, `L = 5`, `w = 1/5`,
`u = 1/4`, power 1, `e = 3/5`, `t = 2/5`, `Φ = −1/19`, `Ψ = 1/28`, `N = 8`. -/
theorem table_Cn :
    zS sCn = 1 ∧ LS sCn = 5 ∧ wS sCn = 1 / 5 ∧ uS sCn = 1 / 4 ∧ powS sCn = 1 ∧
      eS sCn = 3 / 5 ∧ tS sCn = 2 / 5 ∧ PhiS sCn = -1 / 19 ∧ PsiS sCn = 1 / 28 ∧ NS sCn = 8 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rule_values sCn 4 5 1 (by decide) (by decide)
    (by decide)
  have hp : powS sCn = 1 := by rw [powS_eq, show signS sCn = 1 by decide]; norm_num
  have hI4 : I ^ 4 = 1 := Complex.I_pow_four
  refine ⟨by rw [h1, hI4], by rw [h2]; norm_num, by rw [h3, hI4]; norm_num,
    by rw [h4, hI4], hp, by rw [h5]; norm_num, by rw [h6]; norm_num, by rw [h7]; norm_num,
    by rw [h8]; norm_num, by decide⟩

end Law

end Comparison

end
