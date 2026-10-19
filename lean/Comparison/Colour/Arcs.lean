module

public import Comparison.Colour.GramTerm
public import Comparison.Colour.Proton
public import Comparison.Existence.Matter
public import Comparison.Existence.Table

/-!
# Book XVI. The proton and gravity: the finite statements (Propositions 87 to 94)

Prop. 86 is `transition_weight` and
`transition_inventory` (Inventory.lean).

**Prop. 87, every arc once.** An arc is a step `s → s'` of the eighty states (`Continues s s'`).
* `card_arcs`: `320` arcs. `arcs_leaving`, `arcs_entering`: four arcs leave the state an arc enters
  and four arcs enter the state an arc leaves, so `P(a → b) = 1/4` is doubly stochastic
  (`arc_rows`, `arc_cols`); `passage_equations`: for every arc `a` the all-ones vector solves
  `v = e_a + v P_a` (`P_a`: `P` with the column of `a` removed).

**Prop. 89, the landing.**
* `landing_unique`: of the twenty arcs out of the singlet, `(∅, t) → (T_s, s)`, the cross term
  `(γ_t ⊗ γ_s)Ω` is `+e_hk` exactly for `t = h`, `s = k`; `landing_hidden`: the landing starts at a
  closed state (a hidden step, no transition).

**Prop. 90, the Gram-determinant term of one direction.**
* `det_six_root`: `det(t^{1/6}·1₆) = t`; `gramTerm_one_direction`: `−log t^{1/6} = log(1/t)/L(Ω)`,
  `= (1/6) log(5/2)` at `t = 2/5`.
* `gramN_levels`: the three pairings of a holder of `n` amplitudes have the Gram
  `(1 + 1/n)·1 − J₃/n` with levels `1 − 2/n` and `1 + 1/n`, ratio `(n + 1)/(n − 2)`;
  `five_lines_only`: with `d = 2k + 1` lines and `n = 2^k` amplitudes, `d/2 = (n + 1)/(n − 2)`
  only at `k = 2`, five lines.

**Prop. 91, the two signed-volume terms.**
* `kept_by_lastDirection`: the rotations that `{h, n}` keeps are `iγ_h` and the six `γ_sγ_t` of the four other
  lines, seven; `kept_rels`: their two-spinor states are `B_h̄`; `moved_by_singlet`: `{n}` moves the five
  `iγ_s`, whose two-spinor states are `B_L`; `gen_rel`: `(gen x ⊗ 1)Ω = c·e_{genIdx x}`, `c ≠ 0`.
* `Bhbar_agree`: `B_h̄ = {e_S ≠ Ω : (γ_h ⊗ γ_h)e_S = e_S}`; `excursion_leaves_singlet`: `S △ T_t = ∅`
  only for `S = T_t`.
* `commutant_singlet`, `commutant_lastDirection`: on P1's real six, a kept rotation that commutes with every kept
  unit rotation is `0` for `{n}` and a multiple of the plane `(n, h)` (the rotation `iγ_h`) for `{h, n}`.
* `BL_from_plane`, `Bhbar_charges`, `availableTransitions_Bhbar`: seen from the plane `{h, k}`, `B_L` holds
  `(N_F, N_C) = (1, 3)` twice and `(2, 2)` three times; `B_h̄` holds `Q = 2/3` three times,
  `−2/3` three times and `0` once; `34` of the `74` available directed edges hold a two-spinor state of `B_h̄`.

**Prop. 92, the steps not taken.** `untaken`: at the arc `(S, t′) → (S △ T_s, s)` the three
continuations not taken are the lines outside the plane `{t′, s}`; `untaken_slope`:
`∂_u[1 + (d − 1)u² − du] = −(d − 2)` at `u = 1/(d − 1)`.

**Prop. 93, gravity's counts.** `flux_counts`: with `n = 2^{d−1}`, `m = nd/2`,
`n(d − 2) = 2(m − n) = 4, 48, 320` at `d = 3, 5, 7`; `edges_count`: `2(40 − 16) = 48 = 3Eℓ`.

**Prop. 94.** `count_and_gramTerm`: `288 = L(Ω)·n(d − 2) = 6·48`; `tau_bounds`:
`τ = 2π/(Eℓ·m_p/m_e)` lies in `(2.1386, 2.1388)·10⁻⁴`.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex Kronecker

/-! ## Prop. 87: every arc once -/

/-- The arcs: the steps `s → s'` of the eighty states. -/
def arcs : Finset (State × State) := Finset.univ.filter fun p => Continues p.1 p.2

theorem card_arcs : arcs.card = 320 := by
  decide +kernel

/-- The arcs that leave the state `s`. -/
theorem arcs_leaving (s : State) :
    (arcs.filter fun b => b.1 = s).card = 4 := by
  have e : arcs.filter (fun b => b.1 = s) =
      (Finset.univ.filter (Continues s)).image fun s'' => (s, s'') := by
    ext ⟨b1, b2⟩
    simp only [arcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨b2, hc, rfl, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨hx, rfl⟩
  rw [e, Finset.card_image_of_injective _ (fun a b h => by simpa using h), card_continuations]

/-- The arcs that enter the state `s`. -/
theorem arcs_entering (s : State) :
    (arcs.filter fun b => b.2 = s).card = 4 := by
  have e : arcs.filter (fun b => b.2 = s) =
      (Finset.univ.filter fun s0 => Continues s0 s).image fun s0 => (s0, s) := by
    ext ⟨b1, b2⟩
    simp only [arcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨b1, hc, rfl, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨hx, rfl⟩
  rw [e, Finset.card_image_of_injective _ (fun a b h => by simpa using h), card_predecessors]

/-- The step of the arcs: `P(a → b) = 1/4` when `b` leaves the state `a` enters. -/
def arcStep (a b : State × State) : ℚ := if b.1 = a.2 then 1 / 4 else 0

/-- **Every row sums to one.** -/
theorem arc_rows (a : State × State) : ∑ b ∈ arcs, arcStep a b = 1 := by
  simp only [arcStep]
  rw [← Finset.sum_filter, Finset.sum_const, arcs_leaving, nsmul_eq_mul]
  norm_num

/-- **Every column sums to one:** the uniform law on the arcs is stationary. -/
theorem arc_cols (b : State × State) : ∑ a ∈ arcs, arcStep a b = 1 := by
  simp only [arcStep]
  rw [← Finset.sum_filter]
  have e : arcs.filter (fun a => b.1 = a.2) = arcs.filter (fun a => a.2 = b.1) := by
    congr 1
    ext a
    exact eq_comm
  rw [e, Finset.sum_const, arcs_entering, nsmul_eq_mul]
  norm_num

/-- **The passage equations:** for every arc `a`, the all-ones vector `v` solves
`v(b) = [b = a] + Σ_c v(c) P_a(c, b)`, `P_a` the step with the column of `a` removed. -/
theorem passage_equations (a b : State × State) :
    (1 : ℚ) = (if b = a then 1 else 0) + ∑ c ∈ arcs, 1 * (if b = a then 0 else arcStep c b) := by
  by_cases hba : b = a
  · simp [hba]
  · simp only [hba, ↓reduceIte, one_mul, zero_add]
    exact (arc_cols b).symm

/-! ## Prop. 89: the landing -/

theorem landing_unique_Z : ∀ t s h k : Fin 5, t ≠ s → h ≠ k →
    (γZ t * γZ s = γZ h * γZ k ↔ t = h ∧ s = k) := by
  decide +kernel

theorem MΩ_mul_J : MΩ * J = (1 / 2 : ℂ) • 1 := by
  rw [MΩ, Matrix.smul_mul, J_mul_J]
  simp

/-- **The landing:** of the twenty arcs out of the singlet, `(∅, t) → (T_s, s)`, the cross term
`(γ_t ⊗ γ_s)Ω` is `+e_hk` exactly when `t = h` and `s = k`. -/
theorem landing_unique (h k t s : Fin 5) (hk : h ≠ k) (ts : t ≠ s) :
    (γ t ⊗ₖ γ s) *ᵥ Ω = planeRel h k ↔ t = h ∧ s = k := by
  rw [pair_on_singlet, planeRel]
  constructor
  · intro e
    rw [Ω, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one,
      Matrix.mul_one] at e
    have e1 := relOf_injective e
    have e2 : γ t * γ s = γ h * γ k := by
      have := congrArg (fun M => (2 : ℂ) • (M * J)) e1
      simp only [Matrix.mul_assoc, MΩ_mul_J, Matrix.mul_smul, Matrix.mul_one, smul_smul] at this
      norm_num at this
      exact this
    have eZ : γZ t * γZ s = γZ h * γZ k := by
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun e2 i) j
      rw [← γZ_map, ← γZ_map, ← γZ_map, ← γZ_map, ← Matrix.map_mul, ← Matrix.map_mul] at this
      simp only [Matrix.map_apply] at this
      exact GaussianInt.toComplex_inj.mp this
    exact (landing_unique_Z t s h k ts hk).mp eZ
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The landing is a hidden step:** it leaves the closed state `(∅, h)`. -/
theorem landing_hidden : ∀ h k : Fin 5, h ≠ k →
    inExcursion h (0, h) = false ∧ Continues (0, h) (transition k 0, k) := by
  decide

/-! ## Prop. 90: the Gram-determinant term of one direction -/

/-- **`det(t^{1/6}·1₆) = t`.** -/
theorem det_six_root (t : ℝ) (ht : 0 ≤ t) :
    ((t ^ ((6 : ℕ)⁻¹ : ℝ)) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).det = t := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    Real.rpow_inv_natCast_pow ht (by norm_num)]

/-- **The Gram-determinant term of one direction:** `−log t^{1/6} = log(1/t)/L(Ω)`, and at `t = 2/5` it is
`(1/6) log(5/2)`. -/
theorem gramTerm_one_direction (t : ℝ) (ht : 0 < t) :
    -Real.log (t ^ ((6 : ℕ)⁻¹ : ℝ)) = Real.log (1 / t) / 6 ∧
      Real.log (1 / (2 / 5 : ℝ)) / 6 = (1 / 6) * Real.log (5 / 2) := by
  constructor
  · rw [Real.log_rpow ht, one_div, Real.log_inv]
    push_cast
    ring
  · rw [show (1 / (2 / 5 : ℝ)) = 5 / 2 by norm_num]
    ring

/-- The Gram of the three pairings of a holder of `n` amplitudes. -/
def gramN (n : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, -1/n, -1/n; -1/n, 1, -1/n; -1/n, -1/n, 1]

/-- **The pairings of `n` amplitudes:** levels `1 − 2/n` on `(1, 1, 1)` and `1 + 1/n` on its
complement, ratio `(n + 1)/(n − 2)`. -/
theorem gramN_levels (n : ℚ) (hn : n ≠ 0) (hn2 : n ≠ 2) :
    gramN n *ᵥ ![1, 1, 1] = (1 - 2 / n) • ![1, 1, 1] ∧
      gramN n *ᵥ ![1, -1, 0] = (1 + 1 / n) • ![1, -1, 0] ∧
      gramN n *ᵥ ![1, 0, -1] = (1 + 1 / n) • ![1, 0, -1] ∧
      (1 + 1 / n) / (1 - 2 / n) = (n + 1) / (n - 2) := by
  have hn2' : n - 2 ≠ 0 := sub_ne_zero.mpr hn2
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [gramN, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · ext i
    fin_cases i <;> simp [gramN, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · ext i
    fin_cases i <;> simp [gramN, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · field_simp

theorem gramN_four : gramN 4 = gram3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gramN, gram3]

/-- **Only at five lines:** with `d = 2k + 1` lines and a holder of `n = 2^k` amplitudes,
`d/2 = (n + 1)/(n − 2)`, i.e. `d(n − 2) = 2(n + 1)`, holds exactly for `k = 2`. -/
theorem five_lines_only (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k + 1 : ℤ) * (2 ^ k - 2) = 2 * (2 ^ k + 1)) ↔ k = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k 3 with hlt | hge
    · interval_cases k
      · norm_num at h
      · rfl
    · exfalso
      have h8 : (8 : ℤ) ≤ 2 ^ k := by
        have : (2 : ℤ) ^ 3 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hge
        simpa using this
      have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast hge
      nlinarith [mul_nonneg (sub_nonneg.mpr h8) (by linarith : (0 : ℤ) ≤ 2 * k - 1)]
  · rintro rfl
    norm_num

/-! ## Prop. 91: the two signed-volume terms -/

/-- **The rotations `{h, n}` keeps:** `iγ_h` and the six `γ_sγ_t` of the four other lines. -/
theorem kept_by_lastDirection : ∀ h : Fin 5,
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 =>
      ((plane x).1 ∈ ({0, h.succ} : Finset (Fin 6)) ↔
        (plane x).2 ∈ ({0, h.succ} : Finset (Fin 6)))).card = 7 := by
  decide

/-- **Their two-spinor states are `B_h̄`.** -/
theorem kept_rels : ∀ h : Fin 5,
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 =>
      ((plane x).1 ∈ ({0, h.succ} : Finset (Fin 6)) ↔
        (plane x).2 ∈ ({0, h.succ} : Finset (Fin 6)))).image genIdx = Bhbar h := by
  decide

/-- **`{n}` moves the five `iγ_s`, whose two-spinor states are `B_L`; it keeps the ten symmetric states.** -/
theorem moved_by_singlet :
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 =>
      ¬((plane x).1 ∈ ({0} : Finset (Fin 6)) ↔ (plane x).2 ∈ ({0} : Finset (Fin 6)))).image
        genIdx = BL ∧
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 =>
      ¬((plane x).1 ∈ ({0} : Finset (Fin 6)) ↔ (plane x).2 ∈ ({0} : Finset (Fin 6)))).card = 5 := by
  decide

theorem kept_iff_plane (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    Kept D x ↔ ((plane x).1 ∈ D ↔ (plane x).2 ∈ D) := kept_iff D x

/-- **The two-spinor state of a rotation:** `(gen x ⊗ 1)Ω = c·e_{genIdx x}` with `c = i/phase ≠ 0`. -/
theorem gen_rel (x : Fin 5 ⊕ Fin 10) :
    (gen x ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = (I * (relPhase (genIdx x))⁻¹) • rel (genIdx x) ∧
      I * (relPhase (genIdx x))⁻¹ ≠ 0 := by
  have hall : ∀ k : Fin 16, relPhase k ≠ 0 := by
    intro k
    fin_cases k <;> simp [relPhase]
  have hp : relPhase (genIdx x) ≠ 0 := hall _
  constructor
  · rw [rel, gen, relOp_eq_obs, Matrix.smul_kronecker, Matrix.smul_kronecker, Matrix.smul_mulVec,
      Matrix.smul_mulVec, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
  · exact mul_ne_zero I_ne_zero (inv_ne_zero hp)

/-- **`B_h̄` are the two-spinor states other than the singlet on which `γ_h ⊗ γ_h` is `+1`.** -/
theorem Bhbar_agree (h : Fin 5) (k : Fin 16) (hk : k ≠ 0) :
    k ∈ Bhbar h ↔ (γ h ⊗ₖ γ h) *ᵥ rel k = rel k := by
  rw [agreement]
  simp only [Bhbar, Finset.mem_filter, Finset.mem_univ, true_and, hk, ne_eq, not_false_eq_true]
  constructor
  · intro hh
    simp [hh]
  · intro e
    by_contra hh
    simp only [hh, ↓reduceIte, neg_smul, one_smul] at e
    have h0 : rel k = 0 := by
      have := congrArg (fun v => v + rel k) e
      simp only [neg_add_cancel] at this
      have h2 : (2 : ℂ) • rel k = 0 := by rw [two_smul]; exact this.symm
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    have := rel_inner k k
    rw [h0] at this
    simp at this

/-- **An excursion leaves and re-enters the singlet through the vector states:** `S △ T_t = ∅` only for
`S = T_t`. -/
theorem excursion_leaves_singlet : ∀ (t : Fin 5) (k : Fin 16), transition t k = 0 ↔ k = transition t 0 := by
  decide

/-- **The commutant at `{n}`:** a kept rotation of P1's real six that commutes with every kept unit
rotation is zero. -/
theorem commutant_singlet (X : Matrix (Fin 6) (Fin 6) ℝ) (hanti : Xᵀ = -X)
    (hkept : X * thetaD {0} = thetaD {0} * X)
    (hcent : ∀ b c : Fin 6, (b ∈ ({0} : Finset (Fin 6)) ↔ c ∈ ({0} : Finset (Fin 6))) →
      X * unitTurn b c = unitTurn b c * X) : X = 0 := by
  ext a b
  rw [Matrix.zero_apply]
  by_cases hab : a = b
  · subst hab
    have := congrFun (congrFun hanti a) a
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  · by_contra hX
    obtain ⟨hside, hthird⟩ := clock_dividedSet {0} X hkept hcent hab hX
    have key : ∀ a b : Fin 6, a ≠ b → (a ∈ ({0} : Finset (Fin 6)) ↔ b ∈ ({0} : Finset (Fin 6))) →
        ∃ c, (c ∈ ({0} : Finset (Fin 6)) ↔ a ∈ ({0} : Finset (Fin 6))) ∧ c ≠ a ∧ c ≠ b := by
      decide
    obtain ⟨c, hc, hca, hcb⟩ := key a b hab hside
    rcases hthird c hc with h | h
    · exact hca h
    · exact hcb h

/-- **The commutant at `{h, n}`:** such a rotation is a multiple of the rotation of the plane `(n, h)`,
the clock `iγ_h`. -/
theorem commutant_lastDirection (h : Fin 5) (X : Matrix (Fin 6) (Fin 6) ℝ) (hanti : Xᵀ = -X)
    (hkept : X * thetaD {0, h.succ} = thetaD {0, h.succ} * X)
    (hcent : ∀ b c : Fin 6, (b ∈ ({0, h.succ} : Finset (Fin 6)) ↔
      c ∈ ({0, h.succ} : Finset (Fin 6))) → X * unitTurn b c = unitTurn b c * X) :
    X = X 0 h.succ • unitTurn 0 h.succ := by
  have hdiag : ∀ a, X a a = 0 := by
    intro a
    have := congrFun (congrFun hanti a) a
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hzero : ∀ a b : Fin 6, a ≠ b → ¬((a = 0 ∧ b = h.succ) ∨ (a = h.succ ∧ b = 0)) →
      X a b = 0 := by
    intro a b hab hnot
    by_contra hX
    obtain ⟨hside, hthird⟩ := clock_dividedSet {0, h.succ} X hkept hcent hab hX
    have key : ∀ h : Fin 5, ∀ a b : Fin 6, a ≠ b →
        ¬((a = 0 ∧ b = h.succ) ∨ (a = h.succ ∧ b = 0)) →
        (a ∈ ({0, h.succ} : Finset (Fin 6)) ↔ b ∈ ({0, h.succ} : Finset (Fin 6))) →
        ∃ c, (c ∈ ({0, h.succ} : Finset (Fin 6)) ↔ a ∈ ({0, h.succ} : Finset (Fin 6))) ∧
          c ≠ a ∧ c ≠ b := by
      decide
    obtain ⟨c, hc, hca, hcb⟩ := key h a b hab hnot hside
    rcases hthird c hc with e | e
    · exact hca e
    · exact hcb e
  have hsym : X h.succ 0 = -X 0 h.succ := by
    have := congrFun (congrFun hanti 0) h.succ
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    exact this
  ext a b
  simp only [Matrix.smul_apply, unitTurn, Matrix.of_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [hdiag]
    have e1 : ¬(a = 0 ∧ a = h.succ) := fun ⟨h1, h2⟩ => Fin.succ_ne_zero h (h2.symm.trans h1)
    have e2 : ¬(a = h.succ ∧ a = 0) := fun ⟨h1, h2⟩ => e1 ⟨h2, h1⟩
    simp [e1, e2]
  · have hs0 : h.succ ≠ 0 := Fin.succ_ne_zero h
    by_cases h1 : a = 0 ∧ b = h.succ
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hs0, Ne.symm hs0]
    · by_cases h2 : a = h.succ ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hs0, Ne.symm hs0, hsym]
      · rw [hzero a b hab (by tauto)]
        simp [h1, h2]

/-- **`B_L` from the plane:** `(N_F, N_C) = (1, 3)` twice and `(2, 2)` three times. -/
theorem BL_from_plane : ∀ h k : Fin 5, h ≠ k →
    (BL.filter fun r => nPlane h k r = 1 ∧ nOut h k r = 3).card = 2 ∧
    (BL.filter fun r => nPlane h k r = 2 ∧ nOut h k r = 2).card = 3 := by
  decide

/-- **`B_h̄` from the plane:** `Q = 2/3` three times, `−2/3` three times, `0` once. -/
theorem Bhbar_charges : ∀ h k : Fin 5, h ≠ k →
    ((Bhbar h).filter fun r => charge3 h k r = 2).card = 3 ∧
    ((Bhbar h).filter fun r => charge3 h k r = -2).card = 3 ∧
    ((Bhbar h).filter fun r => charge3 h k r = 0).card = 1 := by
  decide

/-- **`34` of the `74` available directed edges hold a two-spinor state of `B_h̄`:** `R_ud = 34/74 = 17/37`. -/
theorem availableTransitions_Bhbar : ∀ h : Fin 5, ((excursionStates h).filter fun s => s.1 ∈ Bhbar h).card = 34 := by
  decide +kernel

/-! ## Prop. 92: the steps not taken -/

/-- **The continuations not taken are the lines outside the plane of the step.** -/
theorem untaken : ∀ t' s : Fin 5, t' ≠ s →
    ((Finset.univ.erase t').erase s = outside t' s ∧ (outside t' s).card = 3) := by
  decide

/-- **At a step along `h` the three untaken lines are other than `h`.** -/
theorem untaken_lastDirection : ∀ t' h : Fin 5, t' ≠ h → h ∉ outside t' h := by
  decide

/-- **`d − 2` is minus the slope of the long-range factor at its zero:**
`∂_u[1 + (d − 1)u² − du] = −(d − 2)` at `u = 1/(d − 1)`. -/
theorem untaken_slope (d : ℝ) (hd : d ≠ 1) :
    HasDerivAt (fun u : ℝ => 1 + (d - 1) * u ^ 2 - d * u) (-(d - 2)) (1 / (d - 1)) := by
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  have := ((((hasDerivAt_pow 2 (1 / (d - 1))).const_mul (d - 1)).const_add 1).sub
    ((hasDerivAt_id (1 / (d - 1))).const_mul d))
  refine this.congr_deriv ?_
  have e : (d - 1) * (2 * (1 / (d - 1))) = 2 := by field_simp
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  rw [e]
  ring

/-! ## Prop. 93: gravity's counts -/

/-- **`n(d − 2) = 2(m − n)` with `n = 2^{d−1}`, `m = nd/2`:** `4, 48, 320` at `d = 3, 5, 7`. -/
theorem flux_counts :
    (2 ^ 2 * (3 - 2) : ℕ) = 2 * (2 ^ 2 * 3 / 2 - 2 ^ 2) ∧ (2 ^ 2 * (3 - 2) : ℕ) = 4 ∧
    (2 ^ 4 * (5 - 2) : ℕ) = 2 * (2 ^ 4 * 5 / 2 - 2 ^ 4) ∧ (2 ^ 4 * (5 - 2) : ℕ) = 48 ∧
    (2 ^ 6 * (7 - 2) : ℕ) = 2 * (2 ^ 6 * 7 / 2 - 2 ^ 6) ∧ (2 ^ 6 * (7 - 2) : ℕ) = 320 := by
  norm_num

/-- **At five lines on the sixteen two-spinor states:** `m = 40` (the Clebsch graph),
`2(m − n) = 48 = 3Eℓ`. -/
theorem edges_count :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 ∧
      2 * (40 - 16) = 3 * 16 := by
  exact ⟨card_edges, by norm_num⟩

/-! ## Prop. 94: one count and one Gram-determinant term -/

theorem count_and_gramTerm : (288 : ℕ) = 6 * 48 ∧ (48 : ℕ) = 16 * (5 - 2) := by norm_num

/-- **`τ = 2π/(Eℓ·m_p/m_e)` lies in `(2.1386·10⁻⁴, 2.1388·10⁻⁴)`.** -/
theorem tau_bounds :
    (2.1386e-4 : ℝ) < 2 * Real.pi / (16 * protonPole) ∧
      2 * Real.pi / (16 * protonPole) < 2.1388e-4 := by
  obtain ⟨hl, hu⟩ := protonPole_bounds
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < 16 * protonPole := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

end Comparison

end
