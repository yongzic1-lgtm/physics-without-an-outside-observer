module

public import Comparison.Law.Returns
public import Comparison.Mass

/-!
# The law, V: one line, one operator; the zero turned and moved; mass and strength at one meeting;
the cross covariance of the transitions (Propositions 140, 161, 162, 166, 169)

Built on `Comparison.Mass` (the Perron root, its expansion, the angle of the zero, the shift of the zero).

**Proposition 161, one line, one operator.** `lineWalk w`: the eighty-state walk `B/4` with a
weight `w_t > 0` on every step along `t`, the same at every vertex.
* `lineWalk_isPerron`: **if `λ > 0` solves `Σ_t w_t/(λ + w_t) = 1`, then `λ/4` is the Perron root of
  the weighted walk** (positive right and left eigenvectors, the spectrum bounded by them);
  `singlet_root_of_secular`: then `u = 1/λ` is the root of the singlet meeting's factor,
  `Σ_t 1/(1 + uw_t) − 4 = 0`, and `singlet_weighted_factor` (the Euler completion) makes it a zero of
  `det(I − uθ_∅W(𝐉 − I))`: **the line side's zero and the singlet meeting's zero are one zero.**
* `conj_spectrum`: `det(λ − (𝒳 ⊗ 1)M(𝒳 ⊗ 1)) = det(λ − M)`: the spectrum in the two bases;
  `Bass.lean`: the vertex form with the lines' weights (`bass_line_weights`).

**Proposition 140 and Proposition 167's `δ(S)`: the level.** `uLevel S = 2/(3 + √(9 + 16e^{−S}))`:
* `uLevel_root`: `1 − 3u − 4u²e^{−S} = 0`; `level_factor`: with `e^{−S}` on the steps along one line,
  `Σ_t 1/(1 + uw_t) − 4 = (1 − 3u − 4u²e^{−S})/((1 + u)(1 + ue^{−S}))`.
* `level_perron`: **for every `S`, `1/(4u_c(S))` is the Perron root of `lastDirectionWalk h (−S)`** (the
  level on the steps along `h`, on the eighty states): one operator in the two bases.
* `delta_expansion`: **`δ(S) = log 4u_c(S) = S/5 − (6/125)S² + O(S³)`**, from `lastDirection_velocity` (Proposition 71 on the eighty states).
* `level_value`: `δ(S) = −log((3 + √(9 + 16e^{−S}))/8)`.

**Proposition 140, a phase on one line.**
* `one_line_rate`, `one_line_angle`: **a phase `e^{−iθ}` on the steps along any one line turns the
  long-range zero at `1/5` per unit `θ`**, alike for each of the five directions (`angle_of_zero`).
* `phase_partials`: at the singlet meeting, `∂_u = −16/5` and `∂_{θ_t} = 4i/25` at `(1/4, 0)`, whose
  quotient gives `d log 4u_c = i dθ_t/5`.

**Proposition 162, the bridge.** `availableTransitions_along_rate`: **the weight on the 60 available transitions along `h`
has the first order `60/320 = 3/16`**; with `availableTransitions_angle_rate` (`1836/320`) and
`one_transition_angle_rate` (`1/320`).

**Proposition 166, mass and strength, one meeting.**
* `uniform_null`: `B𝟏 = 4𝟏`, `𝟏ᵀB = 4𝟏ᵀ`; `lKr_u`: `l K_u r = −4` with `r = l = 𝟏/√80`;
  `charX80_ones`: `(𝒳 ⊗ 1)𝟏 = 4 e_∅ ⊗ 𝟏`, `lKr_u_meeting`: `−4` at the singlet meeting as well.
* `level_source`: `l K_j r = (1/4)(64/80) = 1/5`; `level_shift`: **`du_c/dj = 1/20`** (`zero_shift_law` with the source on the steps along `h`).
* `residue_sixteen`: on the sixteen at the critical step, `(ζ − 5)(ζ − A)⁻¹ → 𝐉/16`;
  `residue_values`: **the residue at the singlet `1/16`, the plane source `−10/16 = −5/8`**.

**Proposition 169.** `lastDirection_cross_cov`: `Cov(X^i_0, X^j_k) = (1/5)(−1/4)^k(δ_ij − 1/5)`;
`cross_spread`: **`σ_ij = (3/25)(δ_ij − 1/5)`**, `12/125` on one line and `−3/125` across two;
`first_order_agree`: at first order both limits are `Σ_i S_i/5`.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology Asymptotics Complex

namespace Law

/-! ## The predecessors and successors of a state, by their last-step directions -/

theorem mem_predSet' {s s' : State} : s ∈ predSet s' ↔ Continues s s' := by
  rw [predSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_succSet' {s s' : State} : s' ∈ succSet s ↔ Continues s s' := by
  rw [succSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The four predecessors of a state come one after each other last-step direction. -/
theorem sum_predSet_lastDirection (f : Fin 5 → ℝ) (s' : State) :
    ∑ s ∈ predSet s', f s.2 = ∑ t ∈ Finset.univ.erase s'.2, f t := by
  refine Finset.sum_nbij' (fun s => s.2) (fun t => (transition s'.2 s'.1, t)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_predSet'] at hs
    rw [Finset.mem_erase]
    exact ⟨fun h => hs.1 h.symm, Finset.mem_univ _⟩
  · intro t ht
    rw [Finset.mem_erase] at ht
    rw [mem_predSet']
    exact ⟨fun h => ht.1 h.symm, by rw [transition_transition]⟩
  · intro s hs
    rw [mem_predSet'] at hs
    refine Prod.ext ?_ rfl
    simp only
    rw [hs.2, transition_transition]
  · intro t _
    rfl
  · intro s _
    rfl

/-- The four successors of a state go along each other last-step direction. -/
theorem sum_succSet_lastDirection (f : Fin 5 → ℝ) (s : State) :
    ∑ s' ∈ succSet s, f s'.2 = ∑ t ∈ Finset.univ.erase s.2, f t := by
  refine Finset.sum_nbij' (fun s' => s'.2) (fun t => (transition t s.1, t)) ?_ ?_ ?_ ?_ ?_
  · intro s' hs
    rw [mem_succSet'] at hs
    rw [Finset.mem_erase]
    exact ⟨hs.1, Finset.mem_univ _⟩
  · intro t ht
    rw [Finset.mem_erase] at ht
    rw [mem_succSet']
    exact ⟨ht.1, rfl⟩
  · intro s' hs
    rw [mem_succSet'] at hs
    refine Prod.ext ?_ rfl
    simp only
    rw [hs.2]
  · intro t _
    rfl
  · intro s' _
    rfl

/-! ## Proposition 161: one line, one operator -/

/-- **The walk with a weight `w_t` on every step along `t`**, the same at every vertex. -/
noncomputable def lineWalk (w : Fin 5 → ℝ) : Matrix State State ℝ :=
  (1 / 4 : ℝ) • stepT (fun _ s' => w s'.2)

/-- **The line side's Perron root:** if `λ > 0` solves the singlet meeting's secular equation
`Σ_t w_t/(λ + w_t) = 1`, then `λ/4` is the Perron root of the weighted walk, with the positive
eigenvectors `x_s = w_{t(s)}/(λ + w_{t(s)})` and `y_s = 1/(λ + w_{t(s)})`. -/
theorem lineWalk_isPerron (w : Fin 5 → ℝ) (hw : ∀ t, 0 < w t) (lam : ℝ) (hl : 0 < lam)
    (hsec : ∑ t, w t / (lam + w t) = 1) : IsPerron (lineWalk w) (lam / 4) := by
  have hpos : ∀ t, 0 < lam + w t := fun t => add_pos hl (hw t)
  refine isPerron_of_pos (lineWalk w) ?_ (lam / 4) (by positivity)
    (fun s => w s.2 / (lam + w s.2)) (fun s => 1 / (lam + w s.2))
    (fun s => div_pos (hw s.2) (hpos s.2)) (fun s => div_pos one_pos (hpos s.2)) ?_ ?_
  · intro i j
    simp only [lineWalk, Matrix.smul_apply, stepT, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact mul_nonneg (by norm_num) (hw _).le
    · norm_num
  · funext s'
    rw [lineWalk, Matrix.smul_mulVec, Pi.smul_apply, stepT_mulVec_real]
    simp only [smul_eq_mul, Pi.smul_apply]
    rw [← Finset.mul_sum, sum_predSet_lastDirection (fun t => w t / (lam + w t)) s']
    have herase : ∑ t ∈ Finset.univ.erase s'.2, w t / (lam + w t) =
        1 - w s'.2 / (lam + w s'.2) := by
      rw [← hsec, ← Finset.sum_erase_add _ _ (Finset.mem_univ s'.2)]
      ring
    rw [herase]
    have := (hpos s'.2).ne'
    field_simp
    ring
  · funext s
    rw [lineWalk, Matrix.vecMul_smul, Pi.smul_apply, stepT_vecMul_real]
    simp only [smul_eq_mul, Pi.smul_apply]
    have e : ∑ s' ∈ succSet s, 1 / (lam + w s'.2) * w s'.2 =
        ∑ t ∈ Finset.univ.erase s.2, w t / (lam + w t) := by
      rw [← sum_succSet_lastDirection (fun t => w t / (lam + w t)) s]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [e]
    have herase : ∑ t ∈ Finset.univ.erase s.2, w t / (lam + w t) =
        1 - w s.2 / (lam + w s.2) := by
      rw [← hsec, ← Finset.sum_erase_add _ _ (Finset.mem_univ s.2)]
      ring
    rw [herase]
    have := (hpos s.2).ne'
    field_simp
    ring

/-- **The same zero at the singlet meeting:** `u = 1/λ` is the root of `Σ_t 1/(1 + uw_t) − 4`. -/
theorem singlet_root_of_secular (w : Fin 5 → ℝ) (hw : ∀ t, 0 < w t) (lam : ℝ) (hl : 0 < lam)
    (hsec : ∑ t, w t / (lam + w t) = 1) : ∑ t, 1 / (1 + (1 / lam) * w t) - 4 = 0 := by
  have e : ∀ t, 1 / (1 + (1 / lam) * w t) = 1 - w t / (lam + w t) := by
    intro t
    have h1 := (add_pos hl (hw t)).ne'
    field_simp
    ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hsec]
  norm_num

/-- **The singlet meeting's weighted factor** (Proposition 135 with the Euler completion):
`det(I − uW(𝐉 − I)) = ∏_t(1 + uw_t) · [Σ_t 1/(1 + uw_t) − 4]` where every `1 + uw_t ≠ 0`. -/
theorem singlet_weighted_factor (u : ℝ) (w : Fin 5 → ℝ) (hw : ∀ t, 1 + u * w t ≠ 0) :
    (1 - u • (diagonal w * (Matrix.of fun i j : Fin 5 => if i = j then (0 : ℝ) else 1))).det =
      (∏ t, (1 + u * w t)) * (∑ t, 1 / (1 + u * w t) - 4) := by
  rw [euler_completion]
  have e : ∀ t, w t * ∏ s ∈ Finset.univ.erase t, (1 + u * w s) =
      w t / (1 + u * w t) * ∏ s, (1 + u * w s) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => 1 + u * w s) (Finset.mem_univ t)]
    have h := hw t
    calc w t * ∏ s ∈ Finset.univ.erase t, (1 + u * w s) =
        (w t / (1 + u * w t)) * (1 + u * w t) * ∏ s ∈ Finset.univ.erase t, (1 + u * w s) := by
          rw [div_mul_cancel₀ _ h]
      _ = _ := by ring
  simp only [e]
  rw [← Finset.sum_mul]
  have e1 : ∀ t, 1 / (1 + u * w t) = 1 - u * (w t / (1 + u * w t)) := by
    intro t
    field_simp [hw t]
    ring
  have e2 : ∑ t, 1 / (1 + u * w t) = 5 - u * ∑ t, w t / (1 + u * w t) := by
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
    norm_num
  rw [e2]
  ring

/-- **The spectrum in the two bases:** `det(λ − (𝒳 ⊗ 1)M(𝒳 ⊗ 1)) = det(λ − M)`. -/
theorem conj_spectrum {K : Type*} [Field K] [CharZero K] (M : Matrix State State K) (l : K) :
    (l • (1 : Matrix State State K) - charX80 K * M * charX80 K).det =
      (l • (1 : Matrix State State K) - M).det := by
  have h : l • (1 : Matrix State State K) - charX80 K * M * charX80 K =
      charX80 K * (l • 1 - M) * charX80 K := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      charX80_mul_self]
  rw [h, det_conj_charX80]


/-! ## Proposition 140 and Proposition 167's `δ(S)`: the level -/

/-- The level `e^{−S}` on the steps along `h`, as weights per line. -/
noncomputable def levelW (h : Fin 5) (S : ℝ) : Fin 5 → ℝ := fun t => if t = h then Real.exp (-S) else 1

/-- **The line side's root under the level:** `λ(S) = (3 + √(9 + 16e^{−S}))/2`. -/
noncomputable def lamLevel (S : ℝ) : ℝ := (3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 2

/-- **The singlet meeting's root under the level:** `u_c(S) = 2/(3 + √(9 + 16e^{−S}))`. -/
noncomputable def uLevel (S : ℝ) : ℝ := 2 / (3 + Real.sqrt (9 + 16 * Real.exp (-S)))

/-- **The zero's shift** `δ(S) = log 4u_c(S)`. -/
noncomputable def deltaLevel (S : ℝ) : ℝ := Real.log (4 * uLevel S)

theorem sqrt_level_pos (S : ℝ) : 0 < Real.sqrt (9 + 16 * Real.exp (-S)) :=
  Real.sqrt_pos.mpr (by positivity)

theorem sqrt_level_sq (S : ℝ) :
    Real.sqrt (9 + 16 * Real.exp (-S)) ^ 2 = 9 + 16 * Real.exp (-S) :=
  Real.sq_sqrt (by positivity)

theorem lamLevel_pos (S : ℝ) : 0 < lamLevel S := by
  have := sqrt_level_pos S
  unfold lamLevel
  positivity

/-- `λ² − 3λ − 4e^{−S} = 0`. -/
theorem lamLevel_eq (S : ℝ) : lamLevel S ^ 2 - 3 * lamLevel S - 4 * Real.exp (-S) = 0 := by
  have h := sqrt_level_sq S
  unfold lamLevel
  linear_combination h / 4

theorem uLevel_eq (S : ℝ) : uLevel S = 1 / lamLevel S := by
  unfold uLevel lamLevel
  have := sqrt_level_pos S
  field_simp

/-- **The level's zero at the singlet meeting:** `1 − 3u − 4u²e^{−S} = 0` at `u = u_c(S)`. -/
theorem uLevel_root (S : ℝ) : 1 - 3 * uLevel S - 4 * uLevel S ^ 2 * Real.exp (-S) = 0 := by
  have hl := (lamLevel_pos S).ne'
  have h := lamLevel_eq S
  rw [uLevel_eq]
  field_simp
  linear_combination h

/-- With `e^{−S}` on the steps along one line,
`Σ_t 1/(1 + uw_t) − 4 = (1 − 3u − 4u²e^{−S})/((1 + u)(1 + ue^{−S}))`. -/
theorem level_factor (h : Fin 5) (S u : ℝ) (h1 : 1 + u ≠ 0) (h2 : 1 + u * Real.exp (-S) ≠ 0) :
    ∑ t, 1 / (1 + u * levelW h S t) - 4 =
      (1 - 3 * u - 4 * u ^ 2 * Real.exp (-S)) / ((1 + u) * (1 + u * Real.exp (-S))) := by
  have e : ∑ t, 1 / (1 + u * levelW h S t) = 1 / (1 + u * Real.exp (-S)) + 4 / (1 + u) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
    have hrest : ∑ t ∈ Finset.univ.erase h, 1 / (1 + u * levelW h S t) = 4 / (1 + u) := by
      have : ∀ t ∈ Finset.univ.erase h, 1 / (1 + u * levelW h S t) = 1 / (1 + u) := by
        intro t ht
        rw [Finset.mem_erase] at ht
        simp [levelW, ht.1]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ h)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      ring
    rw [hrest]
    simp [levelW]
  rw [e]
  field_simp
  ring

theorem level_secular (h : Fin 5) (S : ℝ) :
    ∑ t, levelW h S t / (lamLevel S + levelW h S t) = 1 := by
  have hl := lamLevel_pos S
  have hy := Real.exp_pos (-S)
  have e : ∑ t, levelW h S t / (lamLevel S + levelW h S t) =
      Real.exp (-S) / (lamLevel S + Real.exp (-S)) + 4 / (lamLevel S + 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
    have hrest : ∑ t ∈ Finset.univ.erase h, levelW h S t / (lamLevel S + levelW h S t) =
        4 / (lamLevel S + 1) := by
      have : ∀ t ∈ Finset.univ.erase h, levelW h S t / (lamLevel S + levelW h S t) =
          1 / (lamLevel S + 1) := by
        intro t ht
        rw [Finset.mem_erase] at ht
        simp [levelW, ht.1]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ h)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      ring
    rw [hrest]
    simp [levelW]
  rw [e]
  have h1 : lamLevel S + Real.exp (-S) ≠ 0 := by positivity
  have h2 : lamLevel S + 1 ≠ 0 := by positivity
  rw [div_add_div _ _ h1 h2, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  linear_combination (-1 : ℝ) * lamLevel_eq S

/-- walk with the weight `e^{s[along h]}` is the line-weighted walk with the level `e^{−S}`,
`s = −S`. -/
theorem lastDirectionWalk_eq_lineWalk (h : Fin 5) (S : ℝ) : lastDirectionWalk h (-S) = lineWalk (levelW h S) := by
  ext s' s
  simp only [lastDirectionWalk, lineWalk, Matrix.smul_apply, stepT, Matrix.of_apply, alongH, levelW]
  split_ifs <;> simp

/-- **One line, one operator, under the level:** for every `S`, `λ(S)/4 = 1/(4u_c(S))` is the Perron
root of the eighty-state walk with `e^{−S}` on the steps along `h`. -/
theorem level_perron (h : Fin 5) (S : ℝ) : IsPerron (lastDirectionWalk h (-S)) (lamLevel S / 4) := by
  rw [lastDirectionWalk_eq_lineWalk]
  refine lineWalk_isPerron _ (fun t => ?_) _ (lamLevel_pos S) (level_secular h S)
  unfold levelW
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

theorem level_perronRoot (h : Fin 5) :
    ∀ᶠ S in 𝓝 (0 : ℝ), perronRoot (lastDirectionWalk h) (-S) = lamLevel S / 4 := by
  have hneg : Tendsto (fun S : ℝ => -S) (𝓝 0) (𝓝 0) :=
    continuous_neg.tendsto' 0 0 neg_zero
  have hspec := hneg.eventually (perronRoot_spec (lastDirectionWalk_weighted h))
  filter_upwards [hspec] with S hS
  exact perron_unique _ _ _ hS (level_perron h S)

/-- **`δ(S) = −log((3 + √(9 + 16e^{−S}))/8)`.** -/
theorem level_value (S : ℝ) :
    deltaLevel S = -Real.log ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8) := by
  have hq := sqrt_level_pos S
  rw [deltaLevel, uLevel, ← Real.log_inv]
  congr 1
  field_simp
  ring

theorem deltaLevel_eq (S : ℝ) : deltaLevel S = -Real.log (lamLevel S / 4) := by
  rw [level_value, lamLevel]
  congr 2
  ring

/-- **Proposition 140's level and Proposition 167's `δ(S)` to second order:**
`δ(S) = log 4u_c(S) = S/5 − (6/125)S² + O(S³)`, the singlet meeting's root read through the line side's
Perron root (Proposition 161) and Proposition 71 on the eighty states. -/
theorem delta_expansion :
    (fun S : ℝ => deltaLevel S - (S / 5 - 6 / 125 * S ^ 2)) =O[𝓝 0] (fun S : ℝ => S ^ 3) := by
  have hneg : Tendsto (fun S : ℝ => -S) (𝓝 0) (𝓝 0) :=
    continuous_neg.tendsto' 0 0 neg_zero
  have hO := ((lastDirection_velocity 0).2.2).comp_tendsto hneg
  have hb : ((fun s : ℝ => s ^ 3) ∘ fun S : ℝ => -S) =O[𝓝 0] (fun S : ℝ => S ^ 3) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun S => ?_)
    simp [Function.comp, norm_pow, norm_neg]
  refine ((hO.trans hb).neg_left).congr' ?_ EventuallyEq.rfl
  filter_upwards [level_perronRoot 0] with S hS
  simp only [Function.comp_apply]
  rw [hS, deltaLevel_eq]
  ring

/-- The first order alone: `δ(S) = S/5 + O(S²)`. -/
theorem delta_first_order :
    (fun S : ℝ => deltaLevel S - S / 5) =O[𝓝 0] (fun S : ℝ => S ^ 2) := by
  have h1 : (fun S : ℝ => S ^ 3) =O[𝓝 0] (fun S : ℝ => S ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with S hS
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hS
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, one_mul]
    have h0 : 0 ≤ |S| := abs_nonneg S
    nlinarith [pow_le_pow_left₀ h0 hS 2]
  have h2 : (fun S : ℝ => 6 / 125 * S ^ 2) =O[𝓝 0] (fun S : ℝ => S ^ 2) :=
    Asymptotics.isBigO_const_mul_self _ _ _
  have := (delta_expansion.trans h1).sub h2
  refine this.congr' (Filter.Eventually.of_forall fun S => ?_) EventuallyEq.rfl
  ring

/-! ## Proposition 140, a phase on one line: on the eighty states -/

/-- The weight `1` on every step along the line `t`. -/
noncomputable def alongX (t : Fin 5) : Matrix State State ℝ :=
  Matrix.of fun s' _ => if s'.2 = t then 1 else 0

theorem along_count : ∀ t : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ s'.2 = t then 1 else 0 : ℕ) = 64 := by
  decide +kernel

/-- **A fifth of the steps go along any one line:** the rate of the weight on its steps is `1/5`. -/
theorem one_line_rate (t : Fin 5) : piU ⬝ᵥ (hadPow lawP (alongX t) 1 *ᵥ 1) = 1 / 5 := by
  rw [lawP_rate]
  have e : (∑ s : State, ∑ s' : State, (if Continues s s' then alongX t s' s else 0)) =
      ((∑ s : State, ∑ s' : State, (if Continues s s' ∧ s'.2 = t then 1 else 0 : ℕ) : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [alongX, Matrix.of_apply]
    by_cases hc : Continues s s' <;> by_cases ht : s'.2 = t <;> simp [hc, ht]
  rw [e, along_count t]
  norm_num

/-- **A phase `e^{−iθ}` on the steps along one line turns the long-range zero by a fifth of it:**
the eigenvalue `ψ` of the tilted law through `ψ(0) = 1` turns at `−1/5` per unit `θ`, so the zero
`u = 1/(4ψ)` turns at `1/5`, alike for each of the five directions. -/
theorem one_line_angle (t : Fin 5) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF lawP (alongX t) s (ψ s) = 0) ∧
      HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1 / 5 : ℝ)) 0 := by
  obtain ⟨ψ, h0, hz, -, harg⟩ := angle_of_zero lawP (alongX t) piU (lawP_weighted _)
  rw [one_line_rate] at harg
  exact ⟨ψ, h0, hz, harg⟩

/-- At the singlet meeting: `∂_u[4/(1 + u) + 1/(1 + u) − 4] = −16/5` at `u = 1/4`. -/
theorem phase_partial_u :
    HasDerivAt (fun u : ℂ => 5 / (1 + u) - 4) (-16 / 5) (1 / 4) := by
  have h1 : HasDerivAt (fun u : ℂ => 1 + u) 1 (1 / 4) := (hasDerivAt_id (1 / 4 : ℂ)).const_add 1
  have h2 := (h1.inv (by norm_num)).const_mul 5
  have h3 := h2.sub_const 4
  convert h3 using 1
  · funext u
    simp [div_eq_mul_inv]
  · norm_num

/-- At the singlet meeting: `∂_θ 1/(1 + u e^{−iθ}) = 4i/25` at `(u, θ) = (1/4, 0)`. -/
theorem phase_partial_theta :
    HasDerivAt (fun θ : ℝ => (1 + (1 / 4 : ℂ) * Complex.exp (-I * θ))⁻¹) (4 * I / 25) 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => -I * (θ : ℂ)) (-I * 1) 0 := by
    have := (hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (-I)
    simpa using this
  have h2 := (h1.cexp.const_mul (1 / 4 : ℂ)).const_add 1
  have h3 := h2.inv (by simp; norm_num)
  convert h3 using 1
  simp
  ring

/-- **The quotient of the two partials, read at the zero:** `d log 4u_c/dθ_t = i/5`. -/
theorem phase_turn : -(4 * I / 25) / (-16 / 5) / (1 / 4) = I / 5 := by
  ring

/-! ## Proposition 162: the first order a weighting composes -/

/-- The weight `1` on each of the available transitions along `h`. -/
noncomputable def availableTransitionsAlongX (h : Fin 5) : Matrix State State ℝ :=
  Matrix.of fun s' s => if inExcursion h s = true ∧ s'.2 = h then 1 else 0

theorem availableTransitions_along_count : ∀ h : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ inExcursion h s = true ∧ s'.2 = h then 1 else 0 : ℕ) = 60 := by
  decide +kernel

/-- **The weight on the 60 available transitions along `h` has the first order `60/320 = 3/16`.** -/
theorem availableTransitions_along_rate (h : Fin 5) :
    piU ⬝ᵥ (hadPow lawP (availableTransitionsAlongX h) 1 *ᵥ 1) = 3 / 16 := by
  rw [lawP_rate]
  have e : (∑ s : State, ∑ s' : State, (if Continues s s' then availableTransitionsAlongX h s' s else 0)) =
      ((∑ s : State, ∑ s' : State,
        (if Continues s s' ∧ inExcursion h s = true ∧ s'.2 = h then 1 else 0 : ℕ) : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [availableTransitionsAlongX, Matrix.of_apply]
    by_cases hc : Continues s s' <;> by_cases ha : inExcursion h s = true <;>
      by_cases ht : s'.2 = h <;> simp [hc, ha, ht]
  rw [e, availableTransitions_along_count h]
  norm_num

/-! ## Proposition 166: mass and strength, one meeting -/

/-- **Every state has four continuations in and out:** `B𝟏 = 4𝟏` and `𝟏ᵀB = 4𝟏ᵀ`. -/
theorem uniform_null :
    contB *ᵥ (fun _ => (1 : ℚ)) = (4 : ℚ) • (fun _ => 1) ∧
      (fun _ => (1 : ℚ)) ᵥ* contB = (4 : ℚ) • (fun _ => 1) := by
  constructor
  · funext s'
    simp only [Matrix.mulVec, dotProduct, contB, Matrix.of_apply, mul_one, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_boole]
    have := card_predecessors s'
    rw [this]
    norm_num
  · funext s
    simp only [Matrix.vecMul, dotProduct, contB, Matrix.of_apply, one_mul, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_boole]
    have := card_continuations s
    rw [this]
    norm_num

/-- **`l K_u r = −4`** with `r = l = 𝟏/√80` and `K_u = −B`: `−𝟏ᵀB𝟏/80 = −4`. -/
theorem lKr_u : -((fun _ => (1 : ℚ)) ⬝ᵥ (contB *ᵥ fun _ => 1)) / 80 = -4 := by
  rw [uniform_null.1]
  simp [dotProduct, Finset.sum_const, Finset.card_univ, card_state]
  norm_num

/-- **`(𝒳 ⊗ 1)𝟏 = 4 e_∅ ⊗ 𝟏`:** the uniform vector of the eighty states is the singlet meeting's mean
line. -/
theorem charX80_ones :
    charX80 ℚ *ᵥ (fun _ => 1) = fun p => if p.1 = 0 then 4 else 0 := by
  funext ⟨U, t⟩
  simp only [Matrix.mulVec, dotProduct, charX80, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_one]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h := characters_sum U
  simp only [charX, Matrix.of_apply]
  rw [← Finset.sum_div]
  have e : (∑ x, (charTable U x : ℚ)) = ((∑ x, charTable x U : ℤ) : ℚ) := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => by rw [charTable_symm]
  rw [e, h]
  split_ifs <;> norm_num

/-- **`l K_u r = −4` at the singlet meeting as well:** `−(e_∅ ⊗ 𝟏)ᵀ(⊕_U K_U)(e_∅ ⊗ 𝟏)/5 = −4`. -/
theorem lKr_u_meeting :
    -((fun p : State => if p.1 = 0 then (1 : ℚ) else 0) ⬝ᵥ
        (meetBlocks ℚ (lastDirectionK ℚ) *ᵥ fun p => if p.1 = 0 then 1 else 0)) / 5 = -4 := by
  have : ∀ U : Fin 16, ∀ a b : Fin 5,
      lastDirectionK ℚ U a b = (if a ∈ disagreeSet U then -1 else 1) * (if a = b then 0 else 1) := by
    intro U a b
    simp only [lastDirectionK, thetaM, onesM, diagonal_mul, Matrix.sub_apply, Matrix.of_apply,
      Matrix.one_apply, agreeSign, charSign]
    split_ifs <;> simp
  simp only [dotProduct, Matrix.mulVec, meetBlocks, Matrix.of_apply, this]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, disagreeSet]
  norm_num

/-- The steps along `h` as a source on the eighty states. -/
noncomputable def lastDirectionSteps (h : Fin 5) : Matrix State State ℝ := stepT (fun _ s' => alongH h s')

theorem lastDirectionSteps_total (h : Fin 5) :
    (1 : State → ℝ) ⬝ᵥ (lastDirectionSteps h *ᵥ 1) = 64 := by
  have e : (1 : State → ℝ) ⬝ᵥ (lastDirectionSteps h *ᵥ 1) =
      ((∑ s : State, ∑ s' : State, (if Continues s s' ∧ s'.2 = h then 1 else 0 : ℕ) : ℕ) : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, lastDirectionSteps, stepT, Matrix.of_apply, one_mul, mul_one,
      Pi.one_apply]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [alongH]
    by_cases hc : Continues s s' <;> by_cases ht : s'.2 = h <;> simp [hc, ht]
  rw [e, along_count h]
  norm_num

/-- **The level's source at the critical step:** `l K_j r = (1/4)·64/80 = 1/5`. -/
theorem level_source (h : Fin 5) :
    (1 / 4 : ℝ) * ((1 : State → ℝ) ⬝ᵥ (lastDirectionSteps h *ᵥ 1)) / 80 = 1 / 5 := by
  rw [lastDirectionSteps_total]
  norm_num

/-- **`du_c/dj = 1/20`:** with the source `−(1/4)B_h j` (the level `e^{−j}` on the steps along `h` at
first order, at the critical step), the zero of the law moves at `1/20` per unit `j`
(`zero_shift_law`): `−l K_j r/(l K_u r) = −(1/5)/(−4)`. -/
theorem level_shift (h : Fin 5) :
    ∃ ζ : ℝ → ℝ, ζ 0 = 1 / 4 ∧ (∀ᶠ J in 𝓝 0, lawSrc (-(1 / 4 : ℝ) • lastDirectionSteps h) J (ζ J) = 0) ∧
      HasDerivAt ζ (1 / 20) 0 := by
  obtain ⟨ζ, h0, hz, hd⟩ := zero_shift_law (-(1 / 4 : ℝ) • lastDirectionSteps h)
  refine ⟨ζ, h0, hz, ?_⟩
  convert hd using 1
  rw [Matrix.smul_mulVec, dotProduct_smul, lastDirectionSteps_total]
  norm_num

/-! ### The sixteen at the critical step -/

/-- The adjacency of the sixteen over `ℝ`. -/
noncomputable def adj16 : Matrix (Fin 16) (Fin 16) ℝ := ∑ t, transitionK ℝ t

theorem adj16_eq : adj16 = charX ℝ * diagonal (fun U => (charValue U : ℝ)) * charX ℝ := by
  have h := charX_adjacency_charX ℝ
  have hX := charX_mul_self ℝ
  calc adj16 = charX ℝ * (charX ℝ * adj16 * charX ℝ) * charX ℝ := by
        simp only [← Matrix.mul_assoc, hX, Matrix.one_mul]
        rw [Matrix.mul_assoc, hX, Matrix.mul_one]
    _ = _ := by rw [adj16, h]

/-- The resolvent of the sixteen, `(ζ − A)⁻¹ = 𝒳 diag(1/(ζ − λ_U)) 𝒳`. -/
theorem resolvent16 (ζ : ℝ) (hζ : ∀ U, ζ - (charValue U : ℝ) ≠ 0) :
    (ζ • (1 : Matrix (Fin 16) (Fin 16) ℝ) - adj16) *
        (charX ℝ * diagonal (fun U => 1 / (ζ - (charValue U : ℝ))) * charX ℝ) = 1 := by
  have hX := charX_mul_self ℝ
  have h1 : ζ • (1 : Matrix (Fin 16) (Fin 16) ℝ) - adj16 =
      charX ℝ * diagonal (fun U => ζ - (charValue U : ℝ)) * charX ℝ := by
    rw [adj16_eq]
    have : diagonal (fun U => ζ - (charValue U : ℝ)) =
        ζ • (1 : Matrix (Fin 16) (Fin 16) ℝ) - diagonal (fun U => (charValue U : ℝ)) := by
      ext a b
      simp only [diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul]
      split_ifs <;> simp
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hX]
  rw [h1]
  calc charX ℝ * diagonal (fun U => ζ - (charValue U : ℝ)) * charX ℝ *
        (charX ℝ * diagonal (fun U => 1 / (ζ - (charValue U : ℝ))) * charX ℝ)
      = charX ℝ * (diagonal (fun U => ζ - (charValue U : ℝ)) * (charX ℝ * charX ℝ) *
          diagonal (fun U => 1 / (ζ - (charValue U : ℝ)))) * charX ℝ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hX, Matrix.mul_one, diagonal_mul_diagonal]
        have : (diagonal fun U => (ζ - (charValue U : ℝ)) * (1 / (ζ - (charValue U : ℝ)))) = 1 := by
          ext a b
          simp only [diagonal_apply, Matrix.one_apply]
          split_ifs with hab
          · subst hab
            field_simp [hζ a]
          · rfl
        rw [this, Matrix.mul_one, hX]

theorem charX_apply {K : Type*} [Field K] [CharZero K] (U V : Fin 16) :
    charX K U V = (charTable U V : K) / 4 := rfl

theorem charTable_col_zero : ∀ x : Fin 16, charTable x 0 = 1 := by decide

theorem charTable_row_zero : ∀ x : Fin 16, charTable 0 x = 1 := by decide

/-- The residue matrix of the sixteen at `ζ₀ = 5`, `𝒳 e_∅ e_∅ᵀ 𝒳 = 𝐉/16`. -/
theorem residue16_eq :
    charX ℝ * diagonal (fun U : Fin 16 => if U = 0 then (1 : ℝ) else 0) * charX ℝ =
      Matrix.of fun _ _ => 1 / 16 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rw [Finset.sum_eq_single 0]
  · simp only [↓reduceIte, mul_one, charX_apply, charTable_col_zero, charTable_row_zero,
      Matrix.of_apply]
    norm_num
  · intro c _ hc
    simp [hc]
  · simp

theorem charValue_eq_five_iff : ∀ U : Fin 16, (charValue U = 5 ↔ U = 0) := by decide

/-- **The residue of the sixteen at the critical step:** `(ζ − 5)(ζ − A)⁻¹ → 𝐉/16` as `ζ → 5`. -/
theorem residue_sixteen :
    Tendsto (fun ζ : ℝ => (ζ - 5) • (charX ℝ * diagonal (fun U => 1 / (ζ - (charValue U : ℝ))) *
      charX ℝ)) (𝓝[≠] 5) (𝓝 (Matrix.of fun _ _ => 1 / 16)) := by
  rw [← residue16_eq]
  have hg : ∀ U : Fin 16, Tendsto (fun ζ : ℝ => (ζ - 5) * (1 / (ζ - (charValue U : ℝ))))
      (𝓝[≠] 5) (𝓝 (if U = 0 then 1 else 0)) := by
    intro U
    by_cases hU : U = 0
    · subst hU
      simp only [↓reduceIte]
      have : ∀ ζ ∈ ({5}ᶜ : Set ℝ), (ζ - 5) * (1 / (ζ - ((charValue 0 : ℤ) : ℝ))) = 1 := by
        intro ζ hζ
        have h5 : ζ - 5 ≠ 0 := sub_ne_zero.mpr hζ
        have hc : ((charValue 0 : ℤ) : ℝ) = 5 := by
          have : charValue 0 = 5 := by decide
          rw [this]
          norm_num
        rw [hc]
        field_simp
      exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ζ hζ => (this ζ hζ).symm)
    · simp only [hU, ↓reduceIte]
      have hv : (charValue U : ℝ) ≠ 5 := by
        intro h
        have : charValue U = 5 := by exact_mod_cast h
        exact hU ((charValue_eq_five_iff U).mp this)
      have hc : ContinuousAt (fun ζ : ℝ => (ζ - 5) * (1 / (ζ - (charValue U : ℝ)))) 5 := by
        refine (continuous_id.sub continuous_const).continuousAt.mul ?_
        refine (continuousAt_const.div (continuous_id.sub continuous_const).continuousAt ?_)
        intro h
        exact hv (by linarith)
      have := hc.tendsto
      simp only [sub_self, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
  have hvec : Tendsto (fun ζ : ℝ => fun U : Fin 16 => (ζ - 5) * (1 / (ζ - (charValue U : ℝ))))
      (𝓝[≠] 5) (𝓝 (fun U : Fin 16 => if U = 0 then (1 : ℝ) else 0)) := tendsto_pi_nhds.mpr hg
  have hdiagC : Continuous fun v : Fin 16 → ℝ => diagonal v := continuous_id.matrix_diagonal
  have hdiag := (hdiagC.tendsto _).comp hvec
  have hcont : Continuous fun D : Matrix (Fin 16) (Fin 16) ℝ => charX ℝ * D * charX ℝ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hcont.tendsto _).comp hdiag
  refine this.congr' (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Function.comp_apply]
  have e : diagonal (fun U : Fin 16 => (ζ - 5) * (1 / (ζ - (charValue U : ℝ)))) =
      (ζ - 5) • diagonal (fun U : Fin 16 => 1 / (ζ - (charValue U : ℝ))) := by
    ext a b
    simp only [diagonal_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [e, Matrix.mul_smul, Matrix.smul_mul]

/-- **The residue at the singlet is `1/16`; the ten symmetric states carry `10/16`, and the plane source
`−1` on each plane gives `−10/16 = −5/8`.** -/
theorem residue_values :
    (Matrix.of fun _ _ => (1 / 16 : ℝ) : Matrix (Fin 16) (Fin 16) ℝ) 0 0 = 1 / 16 ∧
      (∑ U ∈ Finset.univ.filter (fun U : Fin 16 => (disagreeSet U).card = 2),
        (Matrix.of fun _ _ => (1 / 16 : ℝ) : Matrix (Fin 16) (Fin 16) ℝ) 0 U) = 10 / 16 ∧
      (∑ U ∈ Finset.univ.filter (fun U : Fin 16 => (disagreeSet U).card = 2),
        (Matrix.of fun _ _ => (1 / 16 : ℝ) : Matrix (Fin 16) (Fin 16) ℝ) 0 U * (-1)) = -5 / 8 := by
  have hc : (Finset.univ.filter (fun U : Fin 16 => (disagreeSet U).card = 2)).card = 10 := by
    decide
  simp only [Matrix.of_apply, Finset.sum_const, hc, nsmul_eq_mul]
  norm_num

/-- The critical step on the sixteen: `(1 + 4u²) − uA = (5 − A)/4 = (6 − L)/4` at `u = 1/4`. -/
theorem critical_sixteen :
    (1 + 4 * (1 / 4 : ℝ) ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - (1 / 4 : ℝ) • adj16 =
      (1 / 4 : ℝ) • ((5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - adj16) := by
  rw [smul_sub, smul_smul]
  norm_num

/-! ## Proposition 169: the cross covariance of the lines' transitions -/

/-- **`Cov(X^i_0, X^j_k) = (1/5)(Hᵏ)_ij − 1/25 = (1/5)(−1/4)^k(δ_ij − 1/5)`** for the last-step direction's walk
`H = (𝐉 − I)/4`. -/
theorem lastDirection_cross_cov (i j : Fin 5) (k : ℕ) :
    (1 / 5 : ℚ) * (lastDirectionStep ^ k) i j - (1 / 5) ^ 2 =
      (1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5) := by
  rw [lastDirectionStep_pow]
  simp only [ones5, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **The long-run covariance `σ_ij = Σ_{k ∈ ℤ} Cov(X^i_0, X^j_k) = (3/25)(δ_ij − 1/5)`.** -/
theorem cross_spread (i j : Fin 5) :
    HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) *
        ((1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5)))
      ((3 / 25) * ((if i = j then 1 else 0) - 1 / 5)) := by
  set c : ℝ := (if i = j then 1 else 0) - 1 / 5 with hc
  have hg : HasSum (fun k : ℕ => (-1 / 4 : ℝ) ^ k) (1 - (-1 / 4))⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by norm_num)
  have h := (hg.mul_left (2 * (1 / 5 : ℝ) * c)).sub (hasSum_ite_eq 0 ((1 / 5 : ℝ) * c))
  convert h using 1
  · funext k
    split_ifs with hk
    · subst hk
      simp only [pow_zero]
      ring
    · ring
  · norm_num
    ring

/-- **`12/125` on one line, `−3/125` across two.** -/
theorem cross_values : (3 / 25 : ℝ) * (1 - 1 / 5) = 12 / 125 ∧ (3 / 25 : ℝ) * (0 - 1 / 5) = -3 / 125 := by
  norm_num

/-- **The two limits agree at first order** (Proposition 169's first order): for two levels on the
last-step direction, the line side `δ(S₁) + δ(S₂)` and the meeting side `δ(S₁ + S₂)` both carry `(S₁ + S₂)/5`,
each with a remainder `O(S²)`. -/
theorem two_limits_first_order :
    (fun p : ℝ × ℝ => deltaLevel p.1 + deltaLevel p.2 - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∧
      (fun p : ℝ × ℝ => deltaLevel (p.1 + p.2) - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) := by
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 0) (𝓝 0) :=
    continuous_fst.tendsto' 0 0 rfl
  have hsnd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' 0 0 rfl
  have hsum : Tendsto (fun p : ℝ × ℝ => p.1 + p.2) (𝓝 0) (𝓝 0) :=
    (continuous_fst.add continuous_snd).tendsto' 0 0 (by simp)
  have h1 := delta_first_order.comp_tendsto hfst
  have h2 := delta_first_order.comp_tendsto hsnd
  have h3 := delta_first_order.comp_tendsto hsum
  constructor
  · have hb1 : (fun p : ℝ × ℝ => p.1 ^ 2) =O[𝓝 0] (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg p.2]
    have hb2 : (fun p : ℝ × ℝ => p.2 ^ 2) =O[𝓝 0] (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg p.1]
    have := (h1.trans hb1).add (h2.trans hb2)
    refine this.congr' (Filter.Eventually.of_forall fun p => ?_) EventuallyEq.rfl
    simp only [Function.comp_apply]
    ring
  · exact h3

end Law

end Comparison

end
