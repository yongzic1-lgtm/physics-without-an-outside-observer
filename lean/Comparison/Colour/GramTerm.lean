module

public import Comparison.Colour.Inventory
public import Comparison.Existence.IharaBass

/-!
# Book XIV. The closed Gram-determinant term and the signed-volume terms (Propositions 80, 81)

**Prop. 80, the closed Gram-determinant term.**
* `swap_conjTranspose`, `Eop_conjTranspose`, `swap_mul_swap`, `Eop_mul_Eop`: `P† = P`, `E† = E`,
  `P² = 1`, `E² = 4E`; `trace_one_two`, `trace_swap`, `trace_Eop`, `trace_swap_Eop`: `Tr 1 = 16`,
  `Tr P = Tr E = 4`, `Tr PE = −4` (`PΩ = −Ω`).
* `pairing_gram`: **the three pairings `1, −P, −E` have the Gram `Tr(X_i†X_j)/16 = (5·1 − J₃)/4`**.
* `gram_levels`: its levels `1/2` (on `(1, 1, 1)`) and `5/4`, `5/4`, ratio `5/2`; `trace_gram`:
  `3`, so `ρ = G/Tr G` has levels `1/6, 5/12, 5/12`; `det_F0`: `det(4G/5) = det(1 − J₃/5) = 2/5`.
* `gramTerm_forms`: `(1/6) log(5/2) = −(1/6) log det F₀ = (1/3)·½ log((1 + 3/7)/(1 − 3/7))
  = Σ_i ρ_i log((5/12)/ρ_i)`.
* `stepT_one_eq`: the plain step is `stepOp transitionMat` of Book X; `weight_moves_zero`: with a weight
  `t > 0` on every step, `det(1 − u·tB)` vanishes at `u = 1/(4t)` and nowhere on `[0, 1/(4t))`; the
  zero moves from `1/4` by `log(1/t)` exactly.
* `L_in_pairings`, `trace_L_sq`: `L = 0·1 + (−2)(−P) + (−2)(−E)` and `Tr L²/16 = 6`.

**Prop. 81, the signed-volume terms.** `sgnL k = sgn L(e_k)`; `volume B a = Π_{k ∈ B} a·sgnL k`.
* `card_BL`, `volume_BL`: the five vector states, `V = −a⁵`.
* `card_Bhbar`, `Bhbar_planes`, `volume_Bhbar`: the seven nonempty two-spinor states avoiding `h`, six symmetric states
  and one vector state, `V = −a⁷`; `deriv_volume_Bhbar`: `−V′/Eℓ = (7/16)a⁶`;
  `opened_volumes`: the seven opened six-volumes sum to `−7a⁶`.
* `Bhbar_closed`: with the singlet, the eight two-spinor states avoiding `h` are closed under `△`;
  `singlet_neighbours`: the five transitions from the singlet reach the five vector states.
* `b_forms`: `7/16 = 84/(2(84 + 12)) = (2³ − 1)/2⁴`.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex Kronecker

/-! ## The three pairings -/

theorem swap_conjTranspose : swapᴴ = swap := by
  ext p q
  have e : (q.1 = p.2 ∧ q.2 = p.1) ↔ (p.1 = q.2 ∧ p.2 = q.1) :=
    ⟨fun ⟨a, b⟩ => ⟨b.symm, a.symm⟩, fun ⟨a, b⟩ => ⟨b.symm, a.symm⟩⟩
  simp only [Matrix.conjTranspose_apply, swap, Matrix.of_apply, e]
  split_ifs <;> simp

theorem Eop_conjTranspose : Eopᴴ = Eop := by
  ext p q
  simp only [Matrix.conjTranspose_apply, Eop, Matrix.of_apply, star_mul', star_star]
  rw [show star (4 : ℂ) = 4 by simp]
  ring

theorem swap_mul_swap : swap * swap = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have hv : v = relOf (Matrix.of fun x y => v (x, y)) := rfl
  rw [hv, swap_relOf, swap_relOf, Matrix.transpose_transpose]

theorem Eop_mul_Eop : Eop * Eop = (4 : ℂ) • Eop := by
  rw [mul_Eop, Eop_mulVec, Ω_norm]
  ext p q
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Eop, Matrix.smul_apply]
  ring

theorem swap_mulVec_singlet : swap *ᵥ Ω = -Ω := by
  have := swap_rel 0
  rw [rel_zero] at this
  rw [this]
  have h0 : swapSign 0 = -1 := by decide
  rw [h0]
  simp

theorem trace_one_two : (1 : Matrix Two Two ℂ).trace = 16 := by
  rw [Matrix.trace_one]
  simp

theorem trace_swap : swap.trace = 4 := by
  simp only [Matrix.trace, Matrix.diag, swap, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [Prod.ext_iff]

theorem sum_norm_singlet : ∑ p, Ω p * star (Ω p) = 1 := by
  have := Ω_norm
  simp only [dotProduct, Pi.star_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem trace_Eop : Eop.trace = 4 := by
  simp only [Matrix.trace, Matrix.diag, Eop, Matrix.of_apply]
  simp only [mul_assoc, ← Finset.mul_sum, sum_norm_singlet]
  norm_num

theorem trace_swap_Eop : (swap * Eop).trace = -4 := by
  rw [mul_Eop, swap_mulVec_singlet]
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Pi.neg_apply]
  have : ∀ p, 4 * -Ω p * star (Ω p) = -4 * (Ω p * star (Ω p)) := fun p => by ring
  simp only [this, ← Finset.mul_sum, sum_norm_singlet]
  norm_num

theorem trace_Eop_mul_Eop : (Eop * Eop).trace = 16 := by
  rw [Eop_mul_Eop, Matrix.trace_smul, trace_Eop]
  norm_num

/-- The three pairings of the four ends of two systems: `1, −P, −E`. -/
noncomputable def pairing : Fin 3 → Matrix Two Two ℂ := ![1, -swap, -Eop]

/-- `(5·1 − J₃)/4`. -/
def gram3 : Matrix (Fin 3) (Fin 3) ℚ := !![1, -1/4, -1/4; -1/4, 1, -1/4; -1/4, -1/4, 1]

/-- **The Gram of the three pairings:** `Tr(X_i†X_j)/16 = (5·1 − J₃)/4`. -/
theorem pairing_gram (i j : Fin 3) :
    ((pairing i)ᴴ * pairing j).trace / 16 = (gram3 i j : ℂ) := by
  have tPE : (Eop * swap).trace = -4 := by rw [Matrix.trace_mul_comm, trace_swap_Eop]
  fin_cases i <;> fin_cases j <;>
    simp [pairing, gram3, Matrix.conjTranspose_neg, swap_conjTranspose, Eop_conjTranspose,
      swap_mul_swap, trace_swap, trace_Eop, trace_swap_Eop, tPE,
      trace_Eop_mul_Eop, Matrix.trace_neg] <;> norm_num

theorem gram3_eq : gram3 = (1 / 4 : ℚ) • ((5 : ℚ) • 1 - Matrix.of fun _ _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram3] <;> norm_num

/-- **The two levels:** `1/2` on `(1, 1, 1)` and `5/4` on `(1, −1, 0)`, `(1, 0, −1)`. -/
theorem gram_levels :
    gram3 *ᵥ ![1, 1, 1] = (1 / 2 : ℚ) • ![1, 1, 1] ∧
      gram3 *ᵥ ![1, -1, 0] = (5 / 4 : ℚ) • ![1, -1, 0] ∧
      gram3 *ᵥ ![1, 0, -1] = (5 / 4 : ℚ) • ![1, 0, -1] ∧ (5 / 4 : ℚ) / (1 / 2) = 5 / 2 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;>
  · ext i
    fin_cases i <;> simp [gram3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem trace_gram : gram3.trace = 3 ∧ (1 / 2 : ℚ) / 3 = 1 / 6 ∧ (5 / 4 : ℚ) / 3 = 5 / 12 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp [gram3, Matrix.trace, Fin.sum_univ_three]
  norm_num

/-- **`det F₀ = det(1 − J₃/5) = 2/5 = t`.** -/
theorem det_F0 : ((4 / 5 : ℚ) • gram3).det = 2 / 5 ∧
    (4 / 5 : ℚ) • gram3 = 1 - (1 / 5 : ℚ) • Matrix.of fun _ _ => 1 := by
  constructor
  · rw [Matrix.det_fin_three]
    simp [gram3]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gram3] <;> norm_num

/-- **The closed Gram-determinant term:** `(1/6) log(5/2) = −(1/6) log det F₀ = (1/3) artanh(3/7) =
Σ_i ρ_i log((5/12)/ρ_i)`, with `artanh x = ½ log((1 + x)/(1 − x))`. -/
theorem gramTerm_forms :
    (1 / 6) * Real.log (5 / 2) = -(1 / 6) * Real.log (2 / 5) ∧
      (1 / 6) * Real.log (5 / 2) = (1 / 3) * ((1 / 2) * Real.log ((1 + 3 / 7) / (1 - 3 / 7))) ∧
      (1 / 6) * Real.log (5 / 2) = (1 / 6) * Real.log ((5 / 12) / (1 / 6)) +
        (5 / 12) * Real.log ((5 / 12) / (5 / 12)) + (5 / 12) * Real.log ((5 / 12) / (5 / 12)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, Real.log_inv]
    ring
  · rw [show ((1 + 3 / 7) / (1 - 3 / 7) : ℝ) = 5 / 2 by norm_num]
    ring
  · rw [show ((5 / 12) / (1 / 6) : ℝ) = 5 / 2 by norm_num, div_self (by norm_num), Real.log_one]
    ring

/-! ## A weight on every step moves the zero by `log(1/t)` -/

/-- The plain step is the step of Book X with the transitions of Proposition 14. -/
theorem stepT_one_eq : stepT (fun _ _ => (1 : ℂ)) = stepOp transitionMat := by
  ext ⟨x', t'⟩ ⟨y, t⟩
  simp only [stepT, stepOp, transitionMat, transitionMatZ, Matrix.of_apply, Matrix.map_apply, Continues]
  by_cases h1 : t' = t
  · simp [h1]
  · by_cases h2 : x' = transition t' y
    · simp [h1, h2]
    · simp [h1, h2]

theorem D_plus_pos (v : ℝ) (h0 : 0 ≤ v) (h1 : v < 1 / 4) :
    (1 - v ^ 2) ^ 24 * (1 - v) * (1 - 4 * v) * (1 - v + 4 * v ^ 2) ^ 10 *
      (1 + 3 * v + 4 * v ^ 2) ^ 5 ≠ 0 := by
  have a1 : 0 < 1 - v ^ 2 := by nlinarith
  have a2 : 0 < 1 - v := by linarith
  have a3 : 0 < 1 - 4 * v := by linarith
  have a4 : 0 < 1 - v + 4 * v ^ 2 := by nlinarith
  have a5 : 0 < 1 + 3 * v + 4 * v ^ 2 := by nlinarith
  positivity

/-- **A weight `t` on every step moves the zero to `1/(4t)`:** `det(1 − u·tB)` vanishes at
`u = 1/(4t)` and nowhere on `[0, 1/(4t))`; so `log(4u_c) = log(1/t)`. -/
theorem weight_moves_zero (t : ℝ) (ht : 0 < t) :
    (1 - ((1 / (4 * t) : ℝ) : ℂ) • ((t : ℂ) • stepT (fun _ _ => (1 : ℂ)))).det = 0 ∧
      (∀ u : ℝ, 0 ≤ u → u < 1 / (4 * t) →
        (1 - (u : ℂ) • ((t : ℂ) • stepT (fun _ _ => (1 : ℂ)))).det ≠ 0) ∧
      Real.log (4 * (1 / (4 * t))) = Real.log (1 / t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_smul, stepT_one_eq, D_plus]
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have : ((1 / (4 * t) : ℝ) : ℂ) * (t : ℂ) = 1 / 4 := by
      push_cast
      field_simp
    rw [this]
    ring
  · intro u hu0 hu1
    rw [smul_smul, stepT_one_eq, D_plus]
    have hv : ((u : ℂ) * (t : ℂ)) = ((u * t : ℝ) : ℂ) := by push_cast; ring
    rw [hv]
    have hut0 : 0 ≤ u * t := mul_nonneg hu0 ht.le
    have hut1 : u * t < 1 / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hu1
      linarith
    have := D_plus_pos (u * t) hut0 hut1
    intro hzero
    apply this
    have e : (((1 - (u * t) ^ 2) ^ 24 * (1 - u * t) * (1 - 4 * (u * t)) *
        (1 - u * t + 4 * (u * t) ^ 2) ^ 10 * (1 + 3 * (u * t) + 4 * (u * t) ^ 2) ^ 5 : ℝ) : ℂ) =
        (1 - ((u * t : ℝ) : ℂ) ^ 2) ^ 24 * (1 - ((u * t : ℝ) : ℂ)) * (1 - 4 * ((u * t : ℝ) : ℂ)) *
          (1 - ((u * t : ℝ) : ℂ) + 4 * ((u * t : ℝ) : ℂ) ^ 2) ^ 10 *
          (1 + 3 * ((u * t : ℝ) : ℂ) + 4 * ((u * t : ℝ) : ℂ) ^ 2) ^ 5 := by
      push_cast
      ring
    exact_mod_cast e.trans hzero
  · congr 1
    field_simp

/-! ## The comparison in the pairings -/

/-- **`L = 0·1 + (−2)(−P) + (−2)(−E)`.** -/
theorem L_in_pairings :
    L = (0 : ℂ) • (1 : Matrix Two Two ℂ) + (-2 : ℂ) • (-swap) + (-2 : ℂ) • (-Eop) := by
  rw [L_eq_swap_singlet]
  module

/-- **`Tr L²/16 = 6`.** -/
theorem trace_L_sq : (L * L).trace / 16 = 6 := by
  rw [L_eq_swap_singlet]
  have tPE : (Eop * swap).trace = -4 := by rw [Matrix.trace_mul_comm, trace_swap_Eop]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_smul, Matrix.trace_add, swap_mul_swap, trace_one_two, trace_swap_Eop, tPE,
    trace_Eop_mul_Eop]
  norm_num

/-! ## Prop. 81: the signed-volume terms -/

/-- The sign of the comparison on the two-spinor state `e_k`: `+1` on the singlet and the symmetric states, `−1` on the
vector states. -/
def sgnL (k : Fin 16) : ℤ := if 0 < Lvalue k then 1 else -1

/-- The signed exterior volume `V_B(a) = Π_{k ∈ B} a·sgn L(e_k)`. -/
def volume {R : Type*} [CommRing R] (B : Finset (Fin 16)) (a : R) : R :=
  ∏ k ∈ B, a * (sgnL k : R)

/-- The five vector states. -/
def BL : Finset (Fin 16) := Finset.univ.filter fun k => Lvalue k = -2

/-- The seven nonempty two-spinor states that avoid `h`. -/
def Bhbar (h : Fin 5) : Finset (Fin 16) := Finset.univ.filter fun k => k ≠ 0 ∧ h ∉ disagreeSet k

theorem card_BL : BL.card = 5 ∧ ∏ k ∈ BL, sgnL k = -1 := by decide

theorem card_Bhbar : ∀ h : Fin 5, (Bhbar h).card = 7 ∧ ∏ k ∈ Bhbar h, sgnL k = -1 := by decide

/-- **Six symmetric states and one vector state.** -/
theorem Bhbar_planes : ∀ h : Fin 5, ((Bhbar h).filter fun k => Lvalue k = 2).card = 6 ∧
    ((Bhbar h).filter fun k => Lvalue k = -2).card = 1 := by decide

theorem volume_eq {R : Type*} [CommRing R] (B : Finset (Fin 16)) (a : R) :
    volume B a = a ^ B.card * ((∏ k ∈ B, sgnL k : ℤ) : R) := by
  rw [volume, Finset.prod_mul_distrib, Finset.prod_const, Int.cast_prod]

/-- **`V_{B_L}(a) = −a⁵`.** -/
theorem volume_BL {R : Type*} [CommRing R] (a : R) : volume BL a = -a ^ 5 := by
  rw [volume_eq, card_BL.1, card_BL.2]
  simp

/-- **`V_{B_h̄}(a) = −a⁷`.** -/
theorem volume_Bhbar {R : Type*} [CommRing R] (h : Fin 5) (a : R) :
    volume (Bhbar h) a = -a ^ 7 := by
  rw [volume_eq, (card_Bhbar h).1, (card_Bhbar h).2]
  simp

/-- **`−V′_{B_h̄}(a)/Eℓ = (7/16)a⁶`.** -/
theorem deriv_volume_Bhbar (h : Fin 5) (a : ℝ) :
    HasDerivAt (fun x : ℝ => volume (Bhbar h) x) (-(7 * a ^ 6)) a ∧
      -(-(7 * a ^ 6)) / 16 = (7 / 16) * a ^ 6 := by
  constructor
  · have e : (fun x : ℝ => volume (Bhbar h) x) = fun x => -x ^ 7 := by
      funext x
      exact volume_Bhbar h x
    rw [e]
    exact (hasDerivAt_pow 7 a).neg.congr_deriv (by norm_num)
  · ring

/-- **The seven opened six-volumes:** `Σ_{k ∈ B_h̄} sgn L(e_k) Π_{k' ≠ k} a·sgn L(e_k') = −7a⁶`. -/
theorem opened_volumes {R : Type*} [CommRing R] (h : Fin 5) (a : R) :
    ∑ k ∈ Bhbar h, (sgnL k : R) * ∏ k' ∈ (Bhbar h).erase k, a * (sgnL k' : R) = -(7 * a ^ 6) := by
  have hs : ∀ k ∈ Bhbar h, (sgnL k : R) * ∏ k' ∈ (Bhbar h).erase k, a * (sgnL k' : R) =
      a ^ 6 * ((∏ k' ∈ Bhbar h, sgnL k' : ℤ) : R) := by
    intro k hk
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem hk, (card_Bhbar h).1,
      Int.cast_prod, ← Finset.mul_prod_erase (Bhbar h) (fun k' => (sgnL k' : R)) hk]
    ring
  rw [Finset.sum_congr rfl hs, Finset.sum_const, (card_Bhbar h).1, (card_Bhbar h).2]
  simp

/-- **With the singlet, the eight two-spinor states that avoid `h` are closed under `△`.** -/
theorem Bhbar_closed : ∀ h : Fin 5, ∀ k l : Fin 16, h ∉ disagreeSet k → h ∉ disagreeSet l →
    ∃ m : Fin 16, h ∉ disagreeSet m ∧ disagreeSet m = symmDiff (disagreeSet k) (disagreeSet l) := by
  decide

theorem card_avoid :
    ∀ h : Fin 5, (Finset.univ.filter fun k : Fin 16 => h ∉ disagreeSet k).card = 8 := by
  decide

/-- **The five transitions from the singlet reach the five vector states.** -/
theorem singlet_neighbours : ∀ t : Fin 5, disagreeSet (transition t 0) = Finset.univ.erase t ∧
    Lvalue (transition t 0) = -2 := by
  decide

/-- **`b = 7/16 = Var P/(2(Var P + Var Q)) = (2^{d−2} − 1)/2^{d−1}` at `d = 5`.** -/
theorem b_forms : (7 / 16 : ℚ) = 84 / (2 * (84 + 12)) ∧ (7 / 16 : ℚ) = (2 ^ 3 - 1) / 2 ^ 4 := by
  norm_num

end Comparison

end
