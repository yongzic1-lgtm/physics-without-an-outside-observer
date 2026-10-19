module

public import Comparison.Law.Meetings

/-!
# The law, IV: the returns at a meeting, the meetings together, the long-range zero
(Propositions 132, 133, 138)

**Proposition 132.**
* `loop_pattern`: the last-step direction's shortest return `t → s → t` at the pattern `V` carries `ε_tε_s`;
  `half_loop`, `loop_is_vertical`: **`ε_sε_t = −f_sf_tf_sf_t`**, the first pairing's vertical loop of
  the same division without its Clifford sign: for any `f_s, f_t` that anticommute and square to the
  signs `θ_D(s), θ_D(t)` of the pattern's division, as the square-root step `f_x = i^{[x∈D]}J_x` on the 64
  sets do (`Existence/Exterior.lean`: `half_anticomm_ne`, `half_mul_self`; that file is not imported
  here, since its name `volume` meets `Colour/GramTerm.lean`'s in one environment).
* `full_cycle`: `det θ_V = (−1)^{|V|}`; `full_cycle_dividedSet`: **`= z_S²`**, `S` the divided set of the
  pattern (Definition 29).
* `first_return_resolvent`: Sherman and Morrison on the walk among the other four lines: with
  `c_s = ε_s/(1 + xε_s)`, `y = c/(1 − xΣc)` solves `(I − x diag ε (𝐉 − I)) y = ε`, so the first return
  is `G = x² ε_t Σc/(1 − xΣc)`; `sum_c_count`: `Σc = A/(1 + x) − (4 − A)/(1 − x)` with `A` agreements.
* `g_closed`: **the five first returns** `g₄ = z²/(4 − 3z)`, `g₃ = z²(2 − z)/(16 − 8z + 3z²)`,
  `g₂ = −z³/(16 + 3z²) = Φ(z)/z`, `g₁ = −z²(2 + z)/(16 + 8z + 3z²)`, `g₀ = −z²/(4 + 3z)`;
  `g_values_one`, `g_values_neg_one`: `1, 1/11, −1/19, −1/9, −1/7` at `z = 1` and
  `1/7, 1/9, 1/19, −1/11, −1` at `z = −1`.
* `short_returns`: **`Tr K_V² = λ² − 5`, `Tr K_V³ = λ³ − 13λ`** at all 32 patterns,
  `λ = 5 − 2|V|`: `(20, 60)`, `(−4, −12)`, `(4, 12)` at the singlet, a plane, a line meeting.

**Proposition 133.**
* `characters_sum`: `Σ_U χ_U(Δ) = 16[Δ = ∅]`.
* `trace_law_pow`: **`Tr B^r = Σ_U Tr K_U^r = 0, 0, 0, 320, 1920, 3840`** (`r = 1, …, 6`);
  `trace_singlet_pow`: `Tr K_∅^r = 0, 20, 60, 260, 1020, 4100`.
* `signed_law_one_thing`: **`det(I − uB₋) = det(I − uB₁)⁴`**, `B₁` the last-step direction's walk on one system's
  four amplitudes; `D_one`: `det(I − uB₁) = (1 − u²)⁶(1 + 3u² + 16u⁴)²`; `trace_B1_four`:
  `Tr B₁⁴ = −80`.

**Proposition 138.**
* `singlet_zero_mode`: `K_∅ 𝟏 = 4·𝟏`; `singlet_factor` (Meetings): `det(I − uK_∅) = (1 + u)⁴(1 − 4u)`;
  `singlet_slope`: its slope at `1/4` is `−4(5/4)⁴`.
* `finite_at_quarter`: every other meeting and counterpart is finite there: `75/64` (symmetric states), `27/32`
  (line meetings), `125/128` (`{t}`), `135/128` (3|3), `81/128` (`{n}`).
* `point_factor_values`: `1 + 4u² − u(a − d)` is `d/2` at `u = 1/4` and `a/2` at `u = −1/4`.
-/

@[expose] public section

namespace Comparison

open Matrix Kronecker

namespace Law

/-! ## Proposition 132: the returns at a meeting -/

theorem patternK_apply {R : Type*} [CommRing R] (V : Finset (Fin 5)) (t s : Fin 5) :
    patternK (R := R) V t s = (if t ∈ V then -1 else 1) * (if t = s then 0 else 1) := by
  simp [patternK, thetaP, diagonal_mul]

/-- **The shortest return** `t → s → t` carries `ε_tε_s`. -/
theorem loop_pattern {R : Type*} [CommRing R] (V : Finset (Fin 5)) {t s : Fin 5} (h : t ≠ s) :
    patternK (R := R) V t s * patternK V s t =
      (if t ∈ V then -1 else 1) * (if s ∈ V then -1 else 1) := by
  rw [patternK_apply, patternK_apply]
  simp [h, Ne.symm h]

/-- **The vertical loop of the square root of the sign:** if `f_x f_y = −f_y f_x` and `f_x² = θ_x`, `f_y² = θ_y`
(scalars), then `f_x f_y f_x f_y = −θ_xθ_y`. -/
theorem half_loop {A : Type*} [Ring A] [Algebra ℂ A] (fx fy : A) (θx θy : ℂ)
    (hanti : fy * fx = -(fx * fy)) (hx : fx * fx = θx • 1) (hy : fy * fy = θy • 1) :
    fx * fy * fx * fy = -((θx * θy) • 1) := by
  calc fx * fy * fx * fy = fx * (fy * fx) * fy := by simp only [mul_assoc]
    _ = fx * (-(fx * fy)) * fy := by rw [hanti]
    _ = -((fx * fx) * (fy * fy)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by rw [hx, hy, smul_mul_smul_comm, one_mul]

/-- The lines of a pattern as a division of the six. -/
def patternDiv (V : Finset (Fin 5)) : Finset (Fin 6) := V.map (Fin.succEmb 5)

theorem mem_patternDiv (V : Finset (Fin 5)) (t : Fin 5) : t.succ ∈ patternDiv V ↔ t ∈ V := by
  simp [patternDiv]

/-- **At a pattern the last-step direction's two-step return is the vertical loop of the same division without its
Clifford sign:** for steps `f_x` with `f_sf_t = −f_tf_s` and `f_x² = θ_D(x)`, `D` the pattern's
lines, `ε_s(V)ε_t(V) • 1 = −f_sf_tf_sf_t`. -/
theorem loop_is_vertical {A : Type*} [Ring A] [Algebra ℂ A] (V : Finset (Fin 5)) (f : Fin 6 → A)
    {s t : Fin 5} (hanti : f t.succ * f s.succ = -(f s.succ * f t.succ))
    (hsq : ∀ x, f x * f x = (if x ∈ patternDiv V then -1 else 1 : ℂ) • 1) :
    (((if s ∈ V then -1 else 1 : ℂ) * (if t ∈ V then -1 else 1)) • 1 : A) =
      -(f s.succ * f t.succ * f s.succ * f t.succ) := by
  rw [half_loop _ _ _ _ hanti (hsq _) (hsq _), neg_neg]
  simp only [mem_patternDiv]

/-- **The full cycle** through the five directions carries `det θ_V = (−1)^{|V|}`. -/
theorem full_cycle {R : Type*} [CommRing R] (V : Finset (Fin 5)) :
    (thetaP (R := R) V).det = (-1) ^ V.card := by
  rw [thetaP, det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow,
    mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The divided set of a pattern (Definition 29): a pattern of at most three lines is named by its lines;
four lines are the vector state of the fifth, `{t, n}`; all five are the singlet's counterpart `{n}`, `{n}`. -/
def patternDividedSet (V : Finset (Fin 5)) : Finset (Fin 6) :=
  if V.card ≤ 3 then V.map (Fin.succEmb 5) else insert 0 (Vᶜ.map (Fin.succEmb 5))

theorem signS_patternDividedSet : ∀ V : Finset (Fin 5), signS (patternDividedSet V) = (-1) ^ V.card := by
  decide

/-- **The full cycle is `z_S²`.** -/
theorem full_cycle_dividedSet (V : Finset (Fin 5)) :
    (thetaP (R := ℂ) V).det = zS (patternDividedSet V) ^ 2 := by
  rw [full_cycle, zS_sq, signS_patternDividedSet]
  push_cast
  rfl

/-- **Sherman and Morrison on the walk among the other four lines:** with `c_s = ε_s/(1 + xε_s)` and
`y = c/(1 − xΣc)`, `(I − x diag ε (𝐉 − I)) y = ε`. -/
theorem first_return_resolvent {K : Type*} [Field K] (x : K) (e : Fin 4 → K)
    (he : ∀ s, 1 + x * e s ≠ 0) (hd : 1 - x * ∑ s, e s / (1 + x * e s) ≠ 0) :
    (1 - x • (diagonal e * (Matrix.of fun i j : Fin 4 => if i = j then (0 : K) else 1))) *ᵥ
        (fun s => (e s / (1 + x * e s)) / (1 - x * ∑ r, e r / (1 + x * e r))) = e := by
  set sc := ∑ r, e r / (1 + x * e r) with hsc
  funext s
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    diagonal_mul, Matrix.of_apply, smul_eq_mul]
  have hsplit : ∀ r, ((if s = r then (1 : K) else 0) - x * (e s * if s = r then 0 else 1)) *
      (e r / (1 + x * e r) / (1 - x * sc)) =
      (if s = r then (1 + x * e s) * (e s / (1 + x * e s) / (1 - x * sc)) else 0) -
        x * e s * (e r / (1 + x * e r) / (1 - x * sc)) := by
    intro r
    split_ifs with h
    · subst h
      ring
    · ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum, ← Finset.sum_div]
  field_simp [he s, hd]
  ring

/-- The sum of the four `c_s` counts the agreements: with the disagreements `W` among the other
four lines, `Σc = (4 − |W|)/(1 + x) − |W|/(1 − x)`. -/
theorem sum_c_count {K : Type*} [Field K] (x : K) (W : Finset (Fin 4)) :
    ∑ s, (if s ∈ W then (-1 : K) else 1) / (1 + x * (if s ∈ W then -1 else 1)) =
      ((4 - W.card : ℕ) : K) / (1 + x) - (W.card : K) / (1 - x) := by
  have h : ∀ s, (if s ∈ W then (-1 : K) else 1) / (1 + x * (if s ∈ W then -1 else 1)) =
      if s ∈ W then -(1 / (1 - x)) else 1 / (1 + x) := by
    intro s
    split_ifs
    · rw [mul_neg_one, ← sub_eq_add_neg, neg_div]
    · rw [mul_one]
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, nsmul_eq_mul, nsmul_eq_mul]
  have hc : (Finset.univ.filter fun t => t ∉ W).card = 4 - W.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff]
    simp [Finset.inter_univ]
  rw [hc]
  ring

/-- The first return with `A` agreements among the other four lines, at `x = z/4`. -/
noncomputable def firstReturn (A : ℕ) (z : ℂ) : ℂ :=
  let x := z / 4
  let sc := (A : ℂ) / (1 + x) - ((4 - A : ℕ) : ℂ) / (1 - x)
  x ^ 2 * sc / (1 - x * sc)

/-- **The first return with `A` agreements**, in closed form:
`G_A(z) = z²(2A − 4 − z)/(16 + (16 − 8A)z + 3z²)`. -/
theorem firstReturn_closed (A : ℕ) (hA : A ≤ 4) (z : ℂ) (h1 : 4 + z ≠ 0) (h2 : 4 - z ≠ 0)
    (hD : 16 + (16 - 8 * (A : ℂ)) * z + 3 * z ^ 2 ≠ 0) :
    firstReturn A z = z ^ 2 * (2 * A - 4 - z) / (16 + (16 - 8 * (A : ℂ)) * z + 3 * z ^ 2) := by
  have h1' : (1 + z / 4) ≠ 0 := by
    intro h
    apply h1
    linear_combination 4 * h
  have h2' : (1 - z / 4) ≠ 0 := by
    intro h
    apply h2
    linear_combination 4 * h
  have h16 : (16 - z ^ 2) ≠ 0 := by
    have : 16 - z ^ 2 = (4 + z) * (4 - z) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  have hcast : ((4 - A : ℕ) : ℂ) = 4 - (A : ℂ) := by
    rw [Nat.cast_sub hA]
    norm_num
  have hsc : (A : ℂ) / (1 + z / 4) - ((4 - A : ℕ) : ℂ) / (1 - z / 4) =
      16 * (2 * A - 4 - z) / (16 - z ^ 2) := by
    rw [hcast, div_sub_div _ _ h1' h2', div_eq_div_iff (mul_ne_zero h1' h2') h16]
    ring
  have hden : 1 - z / 4 * (16 * (2 * A - 4 - z) / (16 - z ^ 2)) =
      (16 + (16 - 8 * (A : ℂ)) * z + 3 * z ^ 2) / (16 - z ^ 2) := by
    rw [eq_div_iff h16, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ h16]
    ring
  simp only [firstReturn]
  rw [hsc, hden, div_div_eq_mul_div, div_left_inj' hD]
  field_simp
  ring

/-- **The five first returns** (`z` away from the poles). -/
theorem g_closed (z : ℂ) (h1 : 4 + z ≠ 0) (h2 : 4 - z ≠ 0) :
    (4 - 3 * z ≠ 0 → firstReturn 4 z = z ^ 2 / (4 - 3 * z)) ∧
    (16 - 8 * z + 3 * z ^ 2 ≠ 0 →
      firstReturn 3 z = z ^ 2 * (2 - z) / (16 - 8 * z + 3 * z ^ 2)) ∧
    (16 + 3 * z ^ 2 ≠ 0 → firstReturn 2 z = -z ^ 3 / (16 + 3 * z ^ 2)) ∧
    (16 + 8 * z + 3 * z ^ 2 ≠ 0 →
      firstReturn 1 z = -z ^ 2 * (2 + z) / (16 + 8 * z + 3 * z ^ 2)) ∧
    (4 + 3 * z ≠ 0 → firstReturn 0 z = -z ^ 2 / (4 + 3 * z)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e : 16 + (16 - 8 * ((4 : ℕ) : ℂ)) * z + 3 * z ^ 2 = (4 - z) * (4 - 3 * z) := by
      push_cast
      ring
    have hD : 16 + (16 - 8 * ((4 : ℕ) : ℂ)) * z + 3 * z ^ 2 ≠ 0 := by
      rw [e]
      exact mul_ne_zero h2 h
    rw [firstReturn_closed 4 le_rfl z h1 h2 hD, e, div_eq_div_iff (mul_ne_zero h2 h) h]
    push_cast
    ring
  · have e : 16 + (16 - 8 * ((3 : ℕ) : ℂ)) * z + 3 * z ^ 2 = 16 - 8 * z + 3 * z ^ 2 := by
      push_cast
      ring
    rw [firstReturn_closed 3 (by norm_num) z h1 h2 (by rw [e]; exact h), e]
    push_cast
    ring
  · have e : 16 + (16 - 8 * ((2 : ℕ) : ℂ)) * z + 3 * z ^ 2 = 16 + 3 * z ^ 2 := by
      push_cast
      ring
    rw [firstReturn_closed 2 (by norm_num) z h1 h2 (by rw [e]; exact h), e]
    push_cast
    ring
  · have e : 16 + (16 - 8 * ((1 : ℕ) : ℂ)) * z + 3 * z ^ 2 = 16 + 8 * z + 3 * z ^ 2 := by
      push_cast
      ring
    rw [firstReturn_closed 1 (by norm_num) z h1 h2 (by rw [e]; exact h), e]
    push_cast
    ring
  · have e : 16 + (16 - 8 * ((0 : ℕ) : ℂ)) * z + 3 * z ^ 2 = (4 + z) * (4 + 3 * z) := by
      push_cast
      ring
    have hD : 16 + (16 - 8 * ((0 : ℕ) : ℂ)) * z + 3 * z ^ 2 ≠ 0 := by
      rw [e]
      exact mul_ne_zero h1 h
    rw [firstReturn_closed 0 (by norm_num) z h1 h2 hD, e, div_eq_div_iff (mul_ne_zero h1 h) h]
    push_cast
    ring

/-- `g₂ = Φ(z)/z`: the colour last-step direction's return at the plane is the signed excursion, one step shorter. -/
theorem g_two_phi (z : ℂ) (hz : z ≠ 0) (h16 : 16 + 3 * z ^ 2 ≠ 0) :
    -z ^ 3 / (16 + 3 * z ^ 2) = Phi z / z := by
  rw [Phi, div_div, div_eq_div_iff h16 (mul_ne_zero h16 hz)]
  ring

/-- **The five first returns at `z = 1`:** `1, 1/11, −1/19, −1/9, −1/7`. -/
theorem g_values_one :
    firstReturn 4 1 = 1 ∧ firstReturn 3 1 = 1 / 11 ∧ firstReturn 2 1 = -1 / 19 ∧
      firstReturn 1 1 = -1 / 9 ∧ firstReturn 0 1 = -1 / 7 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := g_closed 1 (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h4 (by norm_num)]; norm_num
  · rw [h3 (by norm_num)]; norm_num
  · rw [h2 (by norm_num)]; norm_num
  · rw [h1 (by norm_num)]; norm_num
  · rw [h0 (by norm_num)]; norm_num

/-- **At `z = −1`:** `1/7, 1/9, 1/19, −1/11, −1`. -/
theorem g_values_neg_one :
    firstReturn 4 (-1) = 1 / 7 ∧ firstReturn 3 (-1) = 1 / 9 ∧ firstReturn 2 (-1) = 1 / 19 ∧
      firstReturn 1 (-1) = -1 / 11 ∧ firstReturn 0 (-1) = -1 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := g_closed (-1) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h4 (by norm_num)]; norm_num
  · rw [h3 (by norm_num)]; norm_num
  · rw [h2 (by norm_num)]; norm_num
  · rw [h1 (by norm_num)]; norm_num
  · rw [h0 (by norm_num)]; norm_num

/-- The last-step direction's walk at a pattern over `ℤ`. -/
def patternKZ (V : Finset (Fin 5)) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun t s => (if t ∈ V then -1 else 1) * (if t = s then 0 else 1)

/-- **The short returns are fixed by the comparison alone:** at every one of the 32 patterns,
`Tr K_V² = λ² − 5` and `Tr K_V³ = λ³ − 13λ`, `λ = 5 − 2|V|`. -/
theorem short_returns : ∀ V : Finset (Fin 5),
    (patternKZ V * patternKZ V).trace = (5 - 2 * (V.card : ℤ)) ^ 2 - 5 ∧
      (patternKZ V * patternKZ V * patternKZ V).trace =
        (5 - 2 * (V.card : ℤ)) ^ 3 - 13 * (5 - 2 * (V.card : ℤ)) := by
  decide +kernel

/-- The values `(20, 60)`, `(−4, −12)`, `(4, 12)` at the singlet, a plane, a line meeting. -/
theorem short_return_values :
    (5 - 2 * (0 : ℤ)) ^ 2 - 5 = 20 ∧ (5 - 2 * (0 : ℤ)) ^ 3 - 13 * 5 = 60 ∧
      (5 - 2 * (2 : ℤ)) ^ 2 - 5 = -4 ∧ (5 - 2 * (2 : ℤ)) ^ 3 - 13 * 1 = -12 ∧
      (5 - 2 * (4 : ℤ)) ^ 2 - 5 = 4 ∧ (5 - 2 * (4 : ℤ)) ^ 3 - 13 * (-3) = 12 := by
  norm_num

/-! ## Proposition 133: what the sixteen meetings keep together -/

/-- **`Σ_U χ_U(Δ) = 16[Δ = ∅]`.** -/
theorem characters_sum : ∀ Δ : Fin 16, ∑ U, charTable U Δ = if Δ = 0 then 16 else 0 := by
  decide +kernel

/-- The sixteen meetings' walks over `ℤ`. -/
def meetKZ (U : Fin 16) : Matrix (Fin 5) (Fin 5) ℤ := patternKZ (disagreeSet U)

/-- **`Σ_U Tr K_U^r = 0, 0, 0, 320, 1920, 3840`** for `r = 1, …, 6`. -/
theorem sum_trace_meet_pow :
    ∑ U, (meetKZ U).trace = 0 ∧ ∑ U, (meetKZ U ^ 2).trace = 0 ∧
      ∑ U, (meetKZ U ^ 3).trace = 0 ∧ ∑ U, (meetKZ U ^ 4).trace = 320 ∧
      ∑ U, (meetKZ U ^ 5).trace = 1920 ∧ ∑ U, (meetKZ U ^ 6).trace = 3840 := by
  decide +kernel

/-- **`Tr K_∅^r = 0, 20, 60, 260, 1020, 4100`.** -/
theorem trace_singlet_pow :
    (meetKZ 0).trace = 0 ∧ (meetKZ 0 ^ 2).trace = 20 ∧ (meetKZ 0 ^ 3).trace = 60 ∧
      (meetKZ 0 ^ 4).trace = 260 ∧ (meetKZ 0 ^ 5).trace = 1020 ∧
      (meetKZ 0 ^ 6).trace = 4100 := by
  decide +kernel

section Blocks

variable {K : Type*} [Field K] [CharZero K]

theorem meetBlocks_mul (M N : Fin 16 → Matrix (Fin 5) (Fin 5) K) :
    meetBlocks K M * meetBlocks K N = meetBlocks K (fun U => M U * N U) := by
  ext ⟨U, a⟩ ⟨V, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [meetBlocks, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single V]
  · by_cases h : U = V
    · subst h
      simp [Matrix.mul_apply]
    · simp [h]
  · intro W _ hW
    simp [hW]
  · simp

theorem meetBlocks_pow (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) (r : ℕ) :
    meetBlocks K M ^ r = meetBlocks K (fun U => M U ^ r) := by
  induction r with
  | zero =>
    ext ⟨U, a⟩ ⟨V, b⟩
    simp only [pow_zero, Matrix.one_apply, meetBlocks, Matrix.of_apply, Prod.mk.injEq]
    by_cases h : U = V
    · subst h
      simp
    · simp [h]
  | succ r ih =>
    rw [pow_succ, ih, meetBlocks_mul]
    simp only [pow_succ]

theorem trace_meetBlocks (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) :
    (meetBlocks K M).trace = ∑ U, (M U).trace := by
  simp only [Matrix.trace, Matrix.diag, meetBlocks, Matrix.of_apply, ↓reduceIte]
  rw [Fintype.sum_prod_type]

theorem conj_pow (X M : Matrix State State K) (hX : X * X = 1) (r : ℕ) :
    (X * M * X) ^ r = X * M ^ r * X := by
  induction r with
  | zero => simp [hX]
  | succ r ih =>
    rw [pow_succ, ih, pow_succ]
    calc X * M ^ r * X * (X * M * X) = X * M ^ r * (X * X) * M * X := by
          simp only [Matrix.mul_assoc]
      _ = X * (M ^ r * M) * X := by
          rw [hX, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

end Blocks

theorem lastDirectionK_map (U : Fin 16) : lastDirectionK ℚ U = (meetKZ U).map (Int.castRingHom ℚ) := by
  ext a b
  simp only [lastDirectionK, thetaM, onesM, diagonal_mul, Matrix.sub_apply, Matrix.of_apply,
    Matrix.one_apply, agreeSign, charSign, meetKZ, patternKZ, Matrix.map_apply]
  split_ifs <;> simp

/-- **`Tr B^r = Σ_U Tr K_U^r`:** each meeting weighs every closed walk of the last-step direction by the character of
its displacement, and only the sum over the sixteen meetings keeps the closed comparisons. -/
theorem trace_law_eq_meetings (r : ℕ) :
    (contB ^ r).trace = ∑ U, ((meetKZ U ^ r).trace : ℚ) := by
  have h1 : (contB ^ r).trace = (charX80 ℚ * contB ^ r * charX80 ℚ).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, charX80_mul_self, Matrix.one_mul]
  rw [h1, ← conj_pow _ _ (charX80_mul_self ℚ), prop130_B, meetBlocks_pow, trace_meetBlocks]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [lastDirectionK_map, ← Matrix.map_pow, Matrix.trace]
  simp only [Matrix.diag, Matrix.map_apply, eq_intCast, Matrix.trace]
  push_cast
  rfl

/-- **`Tr B^r = 0, 0, 0, 320, 1920, 3840`** (`r = 1, …, 6`) on the eighty states. -/
theorem trace_law_pow :
    (contB ^ 1).trace = 0 ∧ (contB ^ 2).trace = 0 ∧ (contB ^ 3).trace = 0 ∧
      (contB ^ 4).trace = 320 ∧ (contB ^ 5).trace = 1920 ∧ (contB ^ 6).trace = 3840 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sum_trace_meet_pow
  simp only [trace_law_eq_meetings]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pow_one]
    exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6

/-! ### The signed law is one system's walk -/

/-- **The last-step direction's walk on one system's four amplitudes**, `γ_s` applied along `s`. -/
noncomputable def B1 : Matrix (Four × Fin 5) (Four × Fin 5) ℂ := stepOp γ

/-- The regrouping of the eighty signed states as one system's twenty times the other's four. -/
def splitEquiv : (Four × Four) × Fin 5 ≃ (Four × Fin 5) × Four where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem stepOp_lineOnRel_eq :
    stepOp lineOnRel = (B1 ⊗ₖ (1 : Matrix Four Four ℂ)).submatrix splitEquiv splitEquiv := by
  ext ⟨⟨x1, x2⟩, a⟩ ⟨⟨y1, y2⟩, b⟩
  simp only [stepOp, B1, lineOnRel, Matrix.of_apply, Matrix.submatrix_apply, splitEquiv,
    Equiv.coe_fn_mk, Matrix.kroneckerMap_apply]
  split_ifs <;> simp

/-- **The signed law is the last-step direction's walk on one system's four amplitudes, the other's four standing
by:** `det(I − uB₋) = det(I − uB₁)⁴`. -/
theorem signed_law_one_thing (u : ℂ) :
    (1 - u • stepOp lineOnRel).det = (1 - u • B1).det ^ 4 := by
  rw [stepOp_lineOnRel_eq]
  have h : ((1 - u • B1) ⊗ₖ (1 : Matrix Four Four ℂ)).submatrix splitEquiv splitEquiv =
      1 - u • (B1 ⊗ₖ (1 : Matrix Four Four ℂ)).submatrix splitEquiv splitEquiv := by
    ext ⟨⟨x1, x2⟩, a⟩ ⟨⟨y1, y2⟩, b⟩
    simp only [Matrix.submatrix_apply, splitEquiv, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> by_cases h3 : a = b <;> simp [h1, h2, h3]
  rw [← h, det_submatrix_equiv_self, det_kronecker, det_one, one_pow, mul_one]
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem det_one_sub_γ (t : Fin 5) (u : ℂ) : (1 - u • γ t).det = (1 - u ^ 2) ^ 2 := by
  have := det_cone 1 (fun s => if s = t then -u else 0)
  have hs : (∑ s, (if s = t then -u else 0) • γ s) = -(u • γ t) := by
    simp
  have hs2 : (∑ s : Fin 5, (if s = t then -u else 0) ^ 2) = u ^ 2 := by
    simp [ite_pow]
  rw [hs, hs2, one_smul, ← sub_eq_add_neg, one_pow] at this
  exact this

theorem det_vertex_one (u : ℂ) :
    ((1 + 4 * u ^ 2) • (1 : Matrix Four Four ℂ) - u • ∑ t, γ t).det =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
  have := det_cone (1 + 4 * u ^ 2) (fun _ => -u)
  have hs : (∑ s : Fin 5, (-u) • γ s) = -(u • ∑ t, γ t) := by
    rw [Finset.smul_sum]
    simp
  rw [hs, ← sub_eq_add_neg] at this
  rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **`det(I − uB₁) = (1 − u²)⁶(1 + 3u² + 16u⁴)²`.** -/
theorem D_one (u : ℂ) : (1 - u • B1).det = (1 - u ^ 2) ^ 6 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      B1.map Polynomial.C).det)
    (q := (1 - Polynomial.X ^ 2) ^ 6 * (1 + 3 * Polynomial.X ^ 2 + 16 * Polynomial.X ^ 4) ^ 2)
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := ihara_bass γ γ_mul_self u
  simp only [det_one_sub_γ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vertex_one, Fintype.card_prod] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h14 : (1 - u ^ 2) ^ 14 ≠ 0 := pow_ne_zero _ hc
  apply mul_left_cancel₀ h14
  rw [B1]
  linear_combination h

/-- `B₁` over the Gaussian integers. -/
def B1Z : Matrix (Four × Fin 5) (Four × Fin 5) GaussianInt := stepOp γZ

theorem B1Z_map : B1Z.map GaussianInt.toComplex = B1 := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [B1Z, B1, stepOp, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · simp
  · rw [← γZ_map]
    rfl

theorem trace_B1Z_four : (B1Z * B1Z * (B1Z * B1Z)).trace = -80 := by
  decide +kernel

/-- **`Tr B₁⁴ = −80`:** the twenty squares `tsts` each return `tr(γ_tγ_sγ_tγ_s) = −4`. -/
theorem trace_B1_four : (B1 ^ 4).trace = -80 := by
  have h := congrArg GaussianInt.toComplex trace_B1Z_four
  rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_mul, B1Z_map] at h
  have e : B1 ^ 4 = B1 * B1 * (B1 * B1) := by
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  rw [e]
  have h' : (B1 * B1 * (B1 * B1)).trace = GaussianInt.toComplex (-80) := h
  rw [h', map_neg, map_ofNat]

/-! ## Proposition 138: the long-range zero is the singlet meeting's -/

/-- `K_∅ = 𝐉 − I` has `4` on the mean line `𝟏`. -/
theorem singlet_zero_mode : patternK (R := ℂ) ∅ *ᵥ (fun _ => 1) = (4 : ℂ) • (fun _ => 1) := by
  funext t
  simp only [Matrix.mulVec, dotProduct, patternK_apply, Finset.notMem_empty, ↓reduceIte, one_mul,
    mul_one, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_five]
  fin_cases t <;> simp <;> norm_num

/-- **The slope of the singlet's factor at `1/4` is `−4(5/4)⁴`.** -/
theorem singlet_slope :
    HasDerivAt (fun u : ℂ => (1 + u) ^ 4 * (1 - 4 * u)) (-4 * (5 / 4) ^ 4) (1 / 4) := by
  have h1 : HasDerivAt (fun u : ℂ => 1 + u) 1 (1 / 4) := (hasDerivAt_id (1 / 4 : ℂ)).const_add 1
  have h2 : HasDerivAt (fun u : ℂ => 1 - 4 * u) (-(4 * 1)) (1 / 4) :=
    ((hasDerivAt_id (1 / 4 : ℂ)).const_mul 4).const_sub 1
  have h3 := (h1.pow 4).mul h2
  convert h3 using 1
  norm_num

/-- **Every other meeting and counterpart is finite at the critical step:** with `1 − u² = 15/16`,
`(1 − u²) det(I − uK_V) = (1 + u)^a(1 − u)^d(1 + 4u² − u(a − d))` gives `75/64` (symmetric states, `d = 2`),
`27/32` (line meetings, `d = 4`), `125/128` (`{t}`, `d = 1`), `135/128` (3|3, `d = 3`) and
`81/128` (`{n}`, `d = 5`). -/
theorem finite_at_quarter (V : Finset (Fin 5)) :
    (V.card = 2 → (1 - (1 / 4 : ℂ) • patternK (R := ℂ) V).det = 75 / 64) ∧
    (V.card = 4 → (1 - (1 / 4 : ℂ) • patternK (R := ℂ) V).det = 27 / 32) ∧
    (V.card = 1 → (1 - (1 / 4 : ℂ) • patternK (R := ℂ) V).det = 125 / 128) ∧
    (V.card = 3 → (1 - (1 / 4 : ℂ) • patternK (R := ℂ) V).det = 135 / 128) ∧
    (V.card = 5 → (1 - (1 / 4 : ℂ) • patternK (R := ℂ) V).det = 81 / 128) := by
  have h := pattern_factor (1 / 4 : ℂ) V
  have hc : (1 - (1 / 4 : ℂ) ^ 2) ≠ 0 := by norm_num
  refine ⟨fun hV => ?_, fun hV => ?_, fun hV => ?_, fun hV => ?_, fun hV => ?_⟩ <;>
  · rw [hV] at h
    apply mul_left_cancel₀ hc
    rw [h]
    norm_num

/-- **The point factor at the critical step counts the divided lines:** `1 + 4u² − u(a − d) = d/2` at `u = 1/4`
and `= a/2` at `u = −1/4`, for `a + d = 5`. -/
theorem point_factor_values (a d : ℂ) (h : a + d = 5) :
    1 + 4 * (1 / 4) ^ 2 - 1 / 4 * (a - d) = d / 2 ∧
      1 + 4 * (-1 / 4) ^ 2 - (-1 / 4) * (a - d) = a / 2 := by
  constructor <;> linear_combination (-1 / 4 : ℂ) * h

end Law

end Comparison

end
