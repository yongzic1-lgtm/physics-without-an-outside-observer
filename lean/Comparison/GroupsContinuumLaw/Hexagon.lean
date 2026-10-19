import Comparison.GroupsContinuumLaw.Chart
import Comparison.GroupsContinuumLaw.Symbol

/-!
# The hexagon density `√5 u⁶ F²/2`

Equations (26) to (28). On the two-sheet chart the transition `t` steps from sheet `0`
by `+b_t` and from sheet `1` by `−b_t`; a word `w` of even length returns to its sheet displaced by
`Σ_j (−1)^j e_{w_j}`, recorded in `disp w : Fin 5 → ℤ`. Proved here:

* `no_local_four_cycle`: no cyclically non-backtracking word of length four has displacement zero;
  `square_disp`: the base square `s,t,s,t` lifts to `2(e_s − e_t)` (26); on the chart,
  `four_words_open`: for `N ≥ 3` no such word closes, while `square_wraps_at_two`: at `N = 2` the
  square is a wrapping loop.
* `local_six_cycle_iff`: **the closed six-words are exactly `s,t,r,s,t,r` with three distinct lines**;
  `local_six_cycle_count`: **sixty** rooted oriented words per vertex; `hex_closes_iff`: for `N ≥ 7`
  a six-word closes on the chart iff its displacement vanishes.
* `closed_word_sign`, `closed_word_trace`: **every closed six-word has Clifford product `−1`**.
* `hexagon_shoelace`: the hexagon's enclosed bivector is `a_{str} = (e_s − e_t) ∧ (e_r − e_t)`;
  `hexagon_area_tensor`: **`Σ_{s<t<r} a_{str,ij} a_{str,kl} = 5(P_ik P_jl − P_il P_jk)`** (27), for all
  `i, j, k, l`; `hexagon_area_norm`: each area has norm squared `3`; `card_hex_triples`: ten triples.
* `cell_volume_det`: for `b_a = e_a − e_4`, `det(b bᵀ) = 5`: the cell volume is `√5 ε⁴`.
* `flux_pairing`, `hexagon_flux_sum`, `hexagon_density`: for a field `F ∈ Λ²(𝟏^⊥)` the hexagon fluxes
  `φ = ε²⟨a_{str}, F⟩` give, per cell volume, **`Σ u⁶φ²/(√5 ε⁴) = √5 u⁶|F|² = (√5/2) u⁶ F_{μν}F_{μν}`**
  (28); `two_orientations`, `hexagon_quadratic_part`: an unoriented signed hexagon contributes
  `−2u⁶cos φ`, whose quadratic part is `u⁶φ²` with remainder at most `u⁶φ⁴/12`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Real

/-! ## Words and their displacement -/

/-- A word of length four is cyclically non-backtracking. -/
def cyc4 (w : Fin 4 → Fin 5) : Prop := ∀ j : Fin 4, w j ≠ w (j + 1)

/-- A word of length six is cyclically non-backtracking. -/
def cyc6 (w : Fin 6 → Fin 5) : Prop := ∀ j : Fin 6, w j ≠ w (j + 1)

instance (w : Fin 4 → Fin 5) : Decidable (cyc4 w) := by unfold cyc4; infer_instance
instance (w : Fin 6 → Fin 5) : Decidable (cyc6 w) := by unfold cyc6; infer_instance

/-- The Kronecker indicator `[a = i]`. -/
def dl (a i : Fin 5) : ℤ := if a = i then 1 else 0

/-- The signed displacement of a word: `disp(w)_i = Σ_j (−1)^j [w_j = i]`. -/
def disp {n : ℕ} (w : Fin n → Fin 5) (i : Fin 5) : ℤ :=
  ∑ j : Fin n, (-1) ^ (j : ℕ) * dl (w j) i

theorem disp4_apply (w : Fin 4 → Fin 5) (i : Fin 5) :
    disp w i = dl (w 0) i - dl (w 1) i + dl (w 2) i - dl (w 3) i := by
  simp only [disp, Fin.sum_univ_four]
  norm_num
  ring

theorem disp6_apply (w : Fin 6 → Fin 5) (i : Fin 5) :
    disp w i = dl (w 0) i - dl (w 1) i + dl (w 2) i - dl (w 3) i + dl (w 4) i - dl (w 5) i := by
  simp only [disp, Fin.sum_univ_six]
  norm_num
  ring

theorem dl_self (a : Fin 5) : dl a a = 1 := by simp [dl]

theorem dl_ne {a i : Fin 5} (h : a ≠ i) : dl a i = 0 := by simp [dl, h]

theorem dl_cases (a i : Fin 5) : dl a i = 0 ∨ dl a i = 1 := by
  unfold dl; split_ifs <;> simp

/-- **No closed non-backtracking word of length four.** -/
theorem no_local_four_cycle (w : Fin 4 → Fin 5) (h : cyc4 w) : disp w ≠ 0 := by
  intro h0
  have e := congrFun h0 (w 0)
  rw [disp4_apply, Pi.zero_apply] at e
  have h01 : w 0 ≠ w 1 := h 0
  have h30 : w 3 ≠ w 0 := by simpa using h 3
  rw [dl_self, dl_ne (Ne.symm h01), dl_ne h30] at e
  rcases dl_cases (w 2) (w 0) with h2 | h2 <;> omega

/-- **The base square `s,t,s,t` lifts to the displacement `2(e_s − e_t)`** (26). -/
theorem square_disp (s t : Fin 5) :
    disp ![s, t, s, t] = fun i => 2 * (dl s i - dl t i) := by
  funext i
  rw [disp4_apply]
  show dl s i - dl t i + dl s i - dl t i = 2 * (dl s i - dl t i)
  ring

theorem square_disp_ne (s t : Fin 5) (hst : s ≠ t) : disp ![s, t, s, t] ≠ 0 := by
  intro h
  have e := congrFun h s
  rw [square_disp, Pi.zero_apply] at e
  beta_reduce at e
  rw [dl_self, dl_ne (Ne.symm hst)] at e
  omega

/-- **The closed six-words are exactly `s,t,r,s,t,r` with three distinct lines.** -/
theorem local_six_cycle_iff (w : Fin 6 → Fin 5) :
    cyc6 w ∧ disp w = 0 ↔
      w 0 ≠ w 1 ∧ w 0 ≠ w 2 ∧ w 1 ≠ w 2 ∧ w 3 = w 0 ∧ w 4 = w 1 ∧ w 5 = w 2 := by
  constructor
  · rintro ⟨hc, hd⟩
    have h01 : w 0 ≠ w 1 := hc 0
    have h12 : w 1 ≠ w 2 := by simpa using hc 1
    have h23 : w 2 ≠ w 3 := by simpa using hc 2
    have h34 : w 3 ≠ w 4 := by simpa using hc 3
    have h45 : w 4 ≠ w 5 := by simpa using hc 4
    have h50 : w 5 ≠ w 0 := by simpa using hc 5
    have d0 := congrFun hd (w 0)
    have d2 := congrFun hd (w 2)
    have d4 := congrFun hd (w 4)
    rw [disp6_apply, Pi.zero_apply] at d0 d2 d4
    have e3 : w 3 = w 0 := by
      by_contra hne
      rw [dl_self, dl_ne (Ne.symm h01), dl_ne hne, dl_ne h50] at d0
      rcases dl_cases (w 2) (w 0) with h2 | h2 <;> rcases dl_cases (w 4) (w 0) with h4 | h4 <;>
        omega
    have e5 : w 5 = w 2 := by
      by_contra hne
      rw [dl_self, dl_ne h12, dl_ne (Ne.symm h23), dl_ne hne] at d2
      rcases dl_cases (w 0) (w 2) with h0 | h0 <;> rcases dl_cases (w 4) (w 2) with h4 | h4 <;>
        omega
    have e4 : w 4 = w 1 := by
      by_contra hne
      rw [dl_self, dl_ne (fun h => hne h.symm), dl_ne h34, dl_ne (Ne.symm h45)] at d4
      rcases dl_cases (w 0) (w 4) with h0 | h0 <;> rcases dl_cases (w 2) (w 4) with h2 | h2 <;>
        omega
    have h02 : w 0 ≠ w 2 := fun h => h23 (by rw [e3, h])
    exact ⟨h01, h02, h12, e3, e4, e5⟩
  · rintro ⟨h01, h02, h12, e3, e4, e5⟩
    refine ⟨?_, ?_⟩
    · intro j
      fin_cases j <;> simp [e3, e4, e5, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]
    · funext i
      rw [disp6_apply, e3, e4, e5, Pi.zero_apply]
      ring

/-- **Sixty rooted oriented closed six-words per vertex.** -/
theorem local_six_cycle_count :
    (Finset.univ.filter (fun w : Fin 6 → Fin 5 => cyc6 w ∧ disp w = 0)).card = 60 := by
  have key : (Finset.univ.filter (fun w : Fin 6 → Fin 5 => cyc6 w ∧ disp w = 0)).card =
      (Finset.univ.filter (fun p : Fin 5 × Fin 5 × Fin 5 =>
        p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)).card := by
    apply Finset.card_nbij' (fun w => (w 0, w 1, w 2))
      (fun p => ![p.1, p.2.1, p.2.2, p.1, p.2.1, p.2.2])
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      obtain ⟨h01, h02, h12, -, -, -⟩ := (local_six_cycle_iff w).1 hw
      exact ⟨h01, h02, h12⟩
    · rintro ⟨a, b, c⟩ hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      obtain ⟨hab, hac, hbc⟩ := hp
      rw [local_six_cycle_iff]
      simp [hab, hac, hbc]
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
      obtain ⟨-, -, -, e3, e4, e5⟩ := (local_six_cycle_iff w).1 hw
      funext j
      fin_cases j <;> simp [e3, e4, e5]
    · rintro ⟨a, b, c⟩ _
      simp
  rw [key]
  decide

/-! ## The Clifford sign of a closed word -/

/-- The ordered Clifford product along a six-word. -/
noncomputable def wordGamma6 (w : Fin 6 → Fin 5) : Matrix Four Four ℂ :=
  γ (w 0) * γ (w 1) * γ (w 2) * γ (w 3) * γ (w 4) * γ (w 5)

theorem triple_sq_ring {R : Type*} [Ring R] (a b c : R) (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : b * a = -(a * b)) (hac : c * a = -(a * c)) (hbc : c * b = -(b * c)) :
    a * b * c * a * b * c = -1 := by
  calc a * b * c * a * b * c = a * b * (c * a) * b * c := by simp only [mul_assoc]
    _ = -(a * (b * a) * c * b * c) := by
        rw [hac]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = a * a * (b * c * b * c) := by
        rw [hab]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
    _ = b * (c * b) * c := by rw [ha, one_mul]; simp only [mul_assoc]
    _ = -(b * b * (c * c)) := by
        rw [hbc]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [hb, hc, one_mul]

/-- **Every closed six-word carries the Clifford product `−1`.** -/
theorem closed_word_sign (w : Fin 6 → Fin 5) (h : cyc6 w ∧ disp w = 0) :
    wordGamma6 w = -1 := by
  obtain ⟨h01, h02, h12, e3, e4, e5⟩ := (local_six_cycle_iff w).1 h
  rw [wordGamma6, e3, e4, e5]
  exact triple_sq_ring _ _ _ (γ_mul_self _) (γ_mul_self _) (γ_mul_self _)
    (γ_anticomm (Ne.symm h01)) (γ_anticomm (Ne.symm h02)) (γ_anticomm (Ne.symm h12))

theorem closed_word_trace (w : Fin 6 → Fin 5) (h : cyc6 w ∧ disp w = 0) :
    (wordGamma6 w).trace = -4 := by
  rw [closed_word_sign w h, Matrix.trace_neg, Matrix.trace_one]
  simp [Four]

/-! ## The words on the chart -/

variable {N : ℕ} [NeZero N]

/-- Walking a four-letter word on the chart. -/
def walk4 (w : Fin 4 → Fin 5) (x : VN N) : VN N :=
  transitionN (w 3) (transitionN (w 2) (transitionN (w 1) (transitionN (w 0) x)))

/-- Walking a six-letter word on the chart. -/
def walk6 (w : Fin 6 → Fin 5) (x : VN N) : VN N :=
  transitionN (w 5) (transitionN (w 4) (transitionN (w 3) (transitionN (w 2) (transitionN (w 1) (transitionN (w 0) x)))))

theorem bN_eq_dl (t : Fin 5) (i : Fin 4) : bN (N := N) t i = ((dl t i.castSucc : ℤ) : ZMod N) := by
  simp only [bN, dl, Fin.ext_iff, Fin.val_castSucc]
  split_ifs with h1 h2 h2 <;> simp_all

theorem walk4_zero (w : Fin 4 → Fin 5) (z : ZN N) :
    walk4 w (z, false) = (z + fun i => ((disp w i.castSucc : ℤ) : ZMod N), false) := by
  simp only [walk4, transitionN, Prod.mk.injEq, and_true]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, bN_eq_dl, disp4_apply]
  push_cast
  ring

theorem walk6_zero (w : Fin 6 → Fin 5) (z : ZN N) :
    walk6 w (z, false) = (z + fun i => ((disp w i.castSucc : ℤ) : ZMod N), false) := by
  simp only [walk6, transitionN, Prod.mk.injEq, and_true]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, bN_eq_dl, disp6_apply]
  push_cast
  ring

theorem disp4_sum (w : Fin 4 → Fin 5) : ∑ i, disp w i = 0 := by
  simp only [disp4_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, dl,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem disp6_sum (w : Fin 6 → Fin 5) : ∑ i, disp w i = 0 := by
  simp only [disp6_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, dl,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem disp4_bound (w : Fin 4 → Fin 5) (i : Fin 5) : |disp w i| ≤ 2 := by
  rw [disp4_apply, abs_le]
  rcases dl_cases (w 0) i with h0 | h0 <;> rcases dl_cases (w 1) i with h1 | h1 <;>
    rcases dl_cases (w 2) i with h2 | h2 <;> rcases dl_cases (w 3) i with h3 | h3 <;>
    constructor <;> omega

theorem disp6_bound (w : Fin 6 → Fin 5) (i : Fin 5) : |disp w i| ≤ 3 := by
  rw [disp6_apply, abs_le]
  rcases dl_cases (w 0) i with h0 | h0 <;> rcases dl_cases (w 1) i with h1 | h1 <;>
    rcases dl_cases (w 2) i with h2 | h2 <;> rcases dl_cases (w 3) i with h3 | h3 <;>
    rcases dl_cases (w 4) i with h4 | h4 <;> rcases dl_cases (w 5) i with h5 | h5 <;>
    constructor <;> omega

theorem cast_eq_zero_of_small (d : ℤ) (B : ℕ) (hd : |d| ≤ B) (hN : B < N) :
    ((d : ZMod N) = 0 ↔ d = 0) := by
  constructor
  · intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact Int.eq_zero_of_abs_lt_dvd h (by omega)
  · intro h; rw [h]; simp

/-- A displacement vanishing on the four chart coordinates vanishes, because its sum is zero. -/
theorem disp_zero_of_chart {d : Fin 5 → ℤ} (hs : ∑ i, d i = 0)
    (h : ∀ i : Fin 4, d i.castSucc = 0) : d = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [Fin.sum_univ_five] at hs
  simp only [Fin.castSucc_zero] at h0
  have h1' : d 1 = 0 := h1
  have h2' : d 2 = 0 := h2
  have h3' : d 3 = 0 := h3
  funext i
  fin_cases i <;> simp <;> omega

theorem walk4_closes_iff (hN : 3 ≤ N) (w : Fin 4 → Fin 5) (z : ZN N) :
    walk4 w (z, false) = (z, false) ↔ disp w = 0 := by
  rw [walk4_zero]
  simp only [Prod.mk.injEq, and_true, add_eq_left]
  constructor
  · intro h
    apply disp_zero_of_chart (disp4_sum w)
    intro i
    have := congrFun h i
    exact (cast_eq_zero_of_small _ 2 (disp4_bound w _) (by omega)).1 this
  · intro h
    funext i
    simp [h]

/-- **On every chart with `N ≥ 3` no non-backtracking four-word closes.** -/
theorem four_words_open (hN : 3 ≤ N) (w : Fin 4 → Fin 5) (hw : cyc4 w) (z : ZN N) :
    walk4 w (z, false) ≠ (z, false) := fun h =>
  no_local_four_cycle w hw ((walk4_closes_iff hN w z).1 h)

/-- **At `N = 2` the base square is a wrapping loop.** -/
theorem square_wraps_at_two (s t : Fin 5) (x : VN 2) : walk4 ![s, t, s, t] x = x := by
  rcases x with ⟨z, b⟩
  have key : ∀ a c e : ZMod 2, e + a - c + a - c = e ∧ e - a + c - a + c = e := by decide
  cases b <;> simp only [walk4, transitionN, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Prod.mk.injEq, and_true] <;>
    funext i <;> simp only [Pi.add_apply, Pi.sub_apply]
  · exact (key _ _ _).1
  · exact (key _ _ _).2

/-- **For `N ≥ 7` a six-word closes on the chart iff its displacement vanishes.** -/
theorem hex_closes_iff (hN : 7 ≤ N) (w : Fin 6 → Fin 5) (z : ZN N) :
    walk6 w (z, false) = (z, false) ↔ disp w = 0 := by
  rw [walk6_zero]
  simp only [Prod.mk.injEq, and_true, add_eq_left]
  constructor
  · intro h
    apply disp_zero_of_chart (disp6_sum w)
    intro i
    have := congrFun h i
    exact (cast_eq_zero_of_small _ 3 (disp6_bound w _) (by omega)).1 this
  · intro h
    funext i
    simp [h]

/-- The hexagon `s,t,r,s,t,r` closes on every chart and from either sheet. -/
theorem hexagon_closes (s t r : Fin 5) (x : VN N) : walk6 ![s, t, r, s, t, r] x = x := by
  rcases x with ⟨z, b⟩
  cases b <;> simp [walk6, transitionN] <;> abel

/-! ## The area of a hexagon -/

/-- The wedge of two vectors, as an antisymmetric array. -/
def wedge {R : Type*} [CommRing R] (p q : Fin 5 → R) (i j : Fin 5) : R := p i * q j - p j * q i

/-- The area bivector `a_{str} = (e_s − e_t) ∧ (e_r − e_t)`. -/
def area (s t r i j : Fin 5) : ℤ :=
  (dl s i - dl t i) * (dl r j - dl t j) - (dl s j - dl t j) * (dl r i - dl t i)

theorem area_eq_wedge (s t r : Fin 5) :
    area s t r = wedge (fun i => dl s i - dl t i) (fun j => dl r j - dl t j) := rfl

/-- The six vertices of the hexagon `s,t,r,s,t,r` from sheet `0`, as partial signed sums. -/
def hexPos {R : Type*} [CommRing R] (vs vt vr : Fin 5 → R) : Fin 6 → Fin 5 → R :=
  ![0, vs, vs - vt, vs - vt + vr, vr - vt, vr]

/-- **The shoelace sum of the hexagon is twice `(v_s − v_t) ∧ (v_r − v_t)`.** -/
theorem hexagon_shoelace {R : Type*} [CommRing R] (vs vt vr : Fin 5 → R) :
    (∑ k : Fin 6, wedge (hexPos vs vt vr k) (hexPos vs vt vr (k + 1))) =
      2 • wedge (vs - vt) (vr - vt) := by
  funext i j
  simp only [Finset.sum_apply, Fin.sum_univ_six, hexPos, wedge, Pi.smul_apply, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, nsmul_eq_mul]
  simp
  ring

/-- The ten triples `s < t < r`. -/
theorem card_hex_triples :
    (Finset.univ.filter (fun p : Fin 5 × Fin 5 × Fin 5 => p.1 < p.2.1 ∧ p.2.1 < p.2.2)).card = 10 := by
  decide

/-- The sum over `s < t < r` written out. -/
theorem sum_triples {M : Type*} [AddCommMonoid M] (f : Fin 5 → Fin 5 → Fin 5 → M) :
    (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5, if s < t ∧ t < r then f s t r else 0) =
      f 0 1 2 + f 0 1 3 + f 0 1 4 + f 0 2 3 + f 0 2 4 + f 0 3 4 + f 1 2 3 + f 1 2 4 + f 1 3 4 +
        f 2 3 4 := by
  simp only [Fin.sum_univ_five]
  simp (config := {decide := true})
  abel

/-- The area tensor, integral form: `5 Σ_{s<t<r} a_{ij} a_{kl} = (5δ_ik − 1)(5δ_jl − 1) − (5δ_il − 1)(5δ_jk − 1)`. -/
theorem hexagon_area_tensor_int : ∀ i j k l : Fin 5,
    5 * (area 0 1 2 i j * area 0 1 2 k l + area 0 1 3 i j * area 0 1 3 k l +
      area 0 1 4 i j * area 0 1 4 k l + area 0 2 3 i j * area 0 2 3 k l +
      area 0 2 4 i j * area 0 2 4 k l + area 0 3 4 i j * area 0 3 4 k l +
      area 1 2 3 i j * area 1 2 3 k l + area 1 2 4 i j * area 1 2 4 k l +
      area 1 3 4 i j * area 1 3 4 k l + area 2 3 4 i j * area 2 3 4 k l) =
      (5 * dl i k - 1) * (5 * dl j l - 1) - (5 * dl i l - 1) * (5 * dl j k - 1) := by
  decide +kernel

/-- The projector `P = I − J/5` onto `𝟏^⊥`. -/
def P5 (i j : Fin 5) : ℚ := (dl i j : ℚ) - 1 / 5

/-- **The hexagon area tensor** (27): `Σ_{s<t<r} a_{str,ij} a_{str,kl} = 5(P_ik P_jl − P_il P_jk)`,
for all `i, j, k, l`, i.e. `Σ a ⊗ a = 5 I` on `Λ²(𝟏^⊥)`. -/
theorem hexagon_area_tensor (i j k l : Fin 5) :
    (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5,
      if s < t ∧ t < r then (area s t r i j : ℚ) * area s t r k l else 0) =
      5 * (P5 i k * P5 j l - P5 i l * P5 j k) := by
  rw [sum_triples (fun s t r => (area s t r i j : ℚ) * area s t r k l)]
  have h := congrArg (fun x : ℤ => (x : ℚ)) (hexagon_area_tensor_int i j k l)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_one] at h
  unfold P5
  linear_combination h / 5

/-- **Each hexagon area has norm squared three.** -/
theorem hexagon_area_norm : ∀ s t r : Fin 5, s ≠ t → t ≠ r → s ≠ r →
    (∑ i : Fin 5, ∑ j : Fin 5, if i < j then area s t r i j ^ 2 else 0) = 3 := by
  decide +kernel

/-! ## The cell volume -/

/-- The chart basis `b_a = e_a − e_4`, `a < 4`. -/
def cellBasis : Matrix (Fin 4) (Fin 5) ℤ := fun a i => dl a.castSucc i - dl 4 i

theorem cellBasis_gram :
    cellBasis * cellBasisᵀ = 1 + replicateCol (Fin 1) (fun _ : Fin 4 => (1 : ℤ)) *
      replicateRow (Fin 1) (fun _ : Fin 4 => (1 : ℤ)) := by
  decide +kernel

/-- **`det(b bᵀ) = 5`: the cell volume is `√5 ε⁴`.** -/
theorem cell_volume_det : (cellBasis * cellBasisᵀ).det = 5 := by
  have h := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (fun _ : Fin 4 => (1 : ℤ))
    (fun _ : Fin 4 => (1 : ℤ))
  rw [cellBasis_gram]
  refine h.trans ?_
  simp [dotProduct]

/-! ## The hexagon flux and the density -/

/-- The flux of `F` through the hexagon `s,t,r`. -/
def flux (F : Fin 5 → Fin 5 → ℝ) (s t r : Fin 5) : ℝ := F s r - F s t - F t r

theorem sum_dl_dl (a b : Fin 5) (G : Fin 5 → Fin 5 → ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 5, (dl a i : ℝ) * dl b j * G i j) = G a b := by
  simp only [dl, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- **The flux is the pairing with the area:** `Σ_{ij} a_{str,ij} F_ij = 2(F_sr − F_st − F_tr)`. -/
theorem flux_pairing (F : Fin 5 → Fin 5 → ℝ) (hA : ∀ i j, F j i = -F i j) (s t r : Fin 5) :
    (∑ i : Fin 5, ∑ j : Fin 5, (area s t r i j : ℝ) * F i j) = 2 * flux F s t r := by
  have key : ∀ i j, (area s t r i j : ℝ) * F i j =
      (dl s i : ℝ) * dl r j * F i j - dl s i * dl t j * F i j - dl t i * dl r j * F i j
      + dl t i * dl t j * F i j - dl r i * dl s j * F i j + dl t i * dl s j * F i j
      + dl r i * dl t j * F i j - dl t i * dl t j * F i j := by
    intro i j
    simp only [area, Int.cast_sub, Int.cast_mul]
    ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_dl_dl]
  simp only [flux]
  linarith [hA s r, hA t r, hA s t]

/-- **Hexagon flux sum:** for `F ∈ Λ²(𝟏^⊥)`, `Σ_{s<t<r} φ_{str}² = (5/2) Σ_{ij} F_ij² = 5|F|²`. -/
theorem hexagon_flux_sum (F : Fin 5 → Fin 5 → ℝ) (hA : ∀ i j, F j i = -F i j)
    (hR : ∀ i, ∑ j, F i j = 0) :
    (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5, if s < t ∧ t < r then flux F s t r ^ 2 else 0) =
      5 / 2 * ∑ i : Fin 5, ∑ j : Fin 5, F i j ^ 2 := by
  rw [sum_triples (fun s t r => flux F s t r ^ 2)]
  have r0 := hR 0; have r1 := hR 1; have r2 := hR 2; have r3 := hR 3
  simp only [Fin.sum_univ_five] at r0 r1 r2 r3 ⊢
  have d0 : F 0 0 = 0 := by linarith [hA 0 0]
  have d1 : F 1 1 = 0 := by linarith [hA 1 1]
  have d2 : F 2 2 = 0 := by linarith [hA 2 2]
  have d3 : F 3 3 = 0 := by linarith [hA 3 3]
  have d4 : F 4 4 = 0 := by linarith [hA 4 4]
  simp only [flux, hA 0 1, hA 0 2, hA 0 3, hA 0 4, hA 1 2, hA 1 3, hA 1 4, hA 2 3, hA 2 4, hA 3 4,
    d0, d1, d2, d3, d4] at r0 r1 r2 r3 ⊢
  have e04 : F 0 4 = -(F 0 1 + F 0 2 + F 0 3) := by linarith
  have e14 : F 1 4 = F 0 1 - F 1 2 - F 1 3 := by linarith
  have e24 : F 2 4 = F 0 2 + F 1 2 - F 2 3 := by linarith
  have e34 : F 3 4 = F 0 3 + F 1 3 + F 2 3 := by linarith
  rw [e04, e14, e24, e34]
  ring

/-- **The hexagon density** (28): with `φ_{str} = ε² (F_sr − F_st − F_tr)`, the ten hexagons of a
cell divided by the cell volume `√5 ε⁴` give `√5 u⁶ |F|²_{Λ²} = (√5/2) u⁶ F_{μν}F_{μν}`. -/
theorem hexagon_density (u ε : ℝ) (hε : ε ≠ 0) (F : Fin 5 → Fin 5 → ℝ)
    (hA : ∀ i j, F j i = -F i j) (hR : ∀ i, ∑ j, F i j = 0) :
    (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5,
        if s < t ∧ t < r then u ^ 6 * (ε ^ 2 * flux F s t r) ^ 2 else 0) / (√5 * ε ^ 4) =
      √5 * u ^ 6 * (1 / 2 * ∑ i : Fin 5, ∑ j : Fin 5, F i j ^ 2) ∧
    (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5,
        if s < t ∧ t < r then u ^ 6 * (ε ^ 2 * flux F s t r) ^ 2 else 0) / (√5 * ε ^ 4) =
      √5 / 2 * u ^ 6 * ∑ i : Fin 5, ∑ j : Fin 5, F i j ^ 2 := by
  have hsum : (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5,
      if s < t ∧ t < r then u ^ 6 * (ε ^ 2 * flux F s t r) ^ 2 else 0) =
      u ^ 6 * ε ^ 4 * (∑ s : Fin 5, ∑ t : Fin 5, ∑ r : Fin 5,
        if s < t ∧ t < r then flux F s t r ^ 2 else 0) := by
    rw [sum_triples, sum_triples (fun s t r => flux F s t r ^ 2)]
    ring
  rw [hsum, hexagon_flux_sum F hA hR]
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : (0 : ℝ) < √5 := Real.sqrt_pos.2 (by norm_num)
  have hε4 : ε ^ 4 ≠ 0 := pow_ne_zero 4 hε
  constructor
  · field_simp
    rw [h5]
    ring
  · field_simp
    rw [h5]
    ring

/-- An unoriented signed hexagon: its two orientations, each with Clifford sign `−1`, contribute
`−2u⁶ cos φ`. -/
theorem two_orientations (u φ : ℝ) :
    -((u : ℂ) ^ 6 * Complex.exp (φ * Complex.I)) - (u : ℂ) ^ 6 * Complex.exp (-φ * Complex.I) =
      ((-2 * u ^ 6 * Real.cos φ : ℝ) : ℂ) := by
  have h := Complex.two_cos (x := (φ : ℂ))
  push_cast
  linear_combination (u : ℂ) ^ 6 * h

/-- **The quadratic part of `−2u⁶ cos φ` is `u⁶φ²`**, with remainder at most `u⁶φ⁴/12`. -/
theorem hexagon_quadratic_part (u φ : ℝ) :
    |(-2 * u ^ 6 * Real.cos φ) - (-2 * u ^ 6 + u ^ 6 * φ ^ 2)| ≤ u ^ 6 * φ ^ 4 / 12 := by
  have hlo := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hhi := cos_le_quartic φ
  have hu : 0 ≤ u ^ 6 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlo hu, mul_le_mul_of_nonneg_left hhi hu]

end Comparison.GroupsContinuumLaw
