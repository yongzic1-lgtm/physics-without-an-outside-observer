module

public import Comparison.Mass.Perron
public import Comparison.Mass.Simple
public import Comparison.Existence.Zero

/-!
# The road to the masses: Proposition 71 on the eighty states, Proposition 78 on the available transitions

The general theorem of `Perron.lean`
(`perron_log`) applied to the two walks of the book.

**The eighty states, the steps along the last-step direction.** `lastDirectionWalk h s = (B/4) ∘ e^{s X}` with
`X = [the step goes along h]`:
* `lastDirectionWalk_weighted`: it is a weighted walk (stochastic, kernels one-dimensional, simple root);
* `lastDirection_velocity`: **`d/ds log ρ(s) = 1/5` at `s = 0` and `log ρ(s) = s/5 + (s²/2)(12/125) + O(s³)`**,
  with the Poisson solution `g = 16/25` on the states whose last-step direction is `h` and `−4/25` on the others;
  `lastDirection_variance_is_spread`: the second-order coefficient `12/125` is the sum `Σ_{k ∈ ℤ} Cov(X₀, X_k)`
  of the covariance series of `Zero.lean` (`lastDirection_spread`): **the second derivative is the
  asymptotic variance**.

**The available transitions of `h`, the transitions weighed by `L(Ω) + [along h]`.** `watchedS h s`: the walk watched on
the seventy-four with the weight `e^{s X}` on each transition, `X = 6 + [the transition goes along h]`, the
hidden steps unweighed:
* `watched_weighted`: it is a weighted walk (`watchedR` is doubly stochastic, its kernels are
  one-dimensional, its adjugate is `κ 𝟏𝟏ᵀ` with `κ ≠ 0` since `D₊'(1/4) ≠ 0`);
* `watched_transition_sum`: **`𝟏ᵀ W₁ 𝟏 = 459`**, the transitions `1712/4 + 400/16 + 384/64`;
* `inventory_velocity` (**Proposition 78**): **`d/ds log ρ_W(s) = 1836/296` at `s = 0`**, and
  `log ρ_W(s) = (1836/296)s + (s²/2)σ²_W + O(s³)` with `σ²_W` in its Poisson form.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology Asymptotics

/-! ## Tools -/

theorem stepT_mulVec_real (w : State → State → ℝ) (v : State → ℝ) (s' : State) :
    (stepT w *ᵥ v) s' = ∑ s ∈ predSet s', w s s' * v s := by
  simp only [stepT, Matrix.mulVec, dotProduct, Matrix.of_apply, predSet, Finset.sum_filter,
    ite_mul, zero_mul]

theorem stepT_vecMul_real (w : State → State → ℝ) (v : State → ℝ) (s : State) :
    (v ᵥ* stepT w) s = ∑ s' ∈ succSet s, v s' * w s s' := by
  simp only [stepT, Matrix.vecMul, dotProduct, Matrix.of_apply, succSet, Finset.sum_filter,
    mul_ite, mul_zero]

/-- `e^{sx} = 1 + sx + s²x²/2 + O(s³)`. -/
theorem exp_taylor2 (x : ℝ) :
    (fun s : ℝ => Real.exp (s * x) - (1 + s * x + s ^ 2 / 2 * x ^ 2)) =O[𝓝 0]
      (fun s : ℝ => s ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (|x| ^ 3)
  have hc : Tendsto (fun s : ℝ => s * x) (𝓝 0) (𝓝 (0 * x)) :=
    (continuous_id.mul continuous_const).tendsto 0
  rw [zero_mul] at hc
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), |s * x| ≤ 1 := by
    have := hc.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with s hs
    rwa [Real.dist_eq, sub_zero] at hs
  filter_upwards [hsmall] with s hs
  have h := Real.exp_bound hs (n := 3) (by norm_num)
  have e1 : (∑ m ∈ Finset.range 3, (s * x) ^ m / (m.factorial : ℝ)) =
      1 + s * x + s ^ 2 / 2 * x ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [e1] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine h.trans ?_
  rw [abs_mul, mul_pow, abs_pow]
  have h1 : 0 ≤ |s| ^ 3 * |x| ^ 3 := by positivity
  norm_num [Nat.factorial]
  nlinarith [abs_nonneg s, abs_nonneg x]

theorem isBigO_cube_mul_left {m n p : Type*} [Fintype n] (C : Matrix m n ℝ)
    (R : ℝ → Matrix n p ℝ) (hR : ∀ i j, (fun s => R s i j) =O[𝓝 0] (fun s : ℝ => s ^ 3))
    (i : m) (j : p) : (fun s => (C * R s) i j) =O[𝓝 0] (fun s : ℝ => s ^ 3) := by
  simp only [Matrix.mul_apply]
  exact Asymptotics.IsBigO.fun_sum fun k _ => (hR k j).const_mul_left (C i k)

/-! ## The eighty states, the steps along the last-step direction -/

section LastDirection

variable (h : Fin 5)

/-- The weight of a step: one when it goes along `h`. -/
def alongH (s' : State) : ℝ := if s'.2 = h then 1 else 0

/-- The walk `B/4` with the weight `e^{s[along h]}` on each step. -/
noncomputable def lastDirectionWalk (s : ℝ) : Matrix State State ℝ :=
  (1 / 4 : ℝ) • stepT (fun _ s' => Real.exp (s * alongH h s'))

/-- Its first derivative at `s = 0`. -/
noncomputable def lastDirectionP1 : Matrix State State ℝ := (1 / 4 : ℝ) • stepT (fun _ s' => alongH h s')

/-- Its second derivative at `s = 0`. -/
noncomputable def lastDirectionP2 : Matrix State State ℝ :=
  (1 / 4 : ℝ) • stepT (fun _ s' => alongH h s' ^ 2)

/-- The uniform law on the eighty states. -/
noncomputable def piU : State → ℝ := fun _ => 1 / 80

theorem lastDirectionP0_mulVec (v : State → ℝ) : ((1 / 4 : ℝ) • stepR) *ᵥ v = v ↔
    stepR *ᵥ v = (4 : ℝ) • v := by
  rw [Matrix.smul_mulVec]
  constructor
  · intro hv
    funext i
    have := congrFun hv i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  · intro hv
    funext i
    have := congrFun hv i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith

theorem lastDirectionP0_vecMul (w : State → ℝ) : w ᵥ* ((1 / 4 : ℝ) • stepR) = w ↔
    w ᵥ* stepR = (4 : ℝ) • w := by
  rw [Matrix.vecMul_smul]
  constructor
  · intro hv
    funext i
    have := congrFun hv i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  · intro hv
    funext i
    have := congrFun hv i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith

theorem sum_piU : ∑ i : State, piU i = 1 := by
  simp [piU, Finset.sum_const, Finset.card_univ, card_state]

/-- **The walk with the weight on the steps along `h` is a weighted walk.** -/
theorem lastDirectionWalk_weighted :
    WeightedWalk (lastDirectionWalk h) ((1 / 4 : ℝ) • stepR) (lastDirectionP1 h) (lastDirectionP2 h) piU where
  nonneg := by
    intro s i j
    simp only [lastDirectionWalk, stepT, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · positivity
    · norm_num
  taylor := by
    intro i j
    by_cases hc : Continues j i
    · have := (exp_taylor2 (alongH h i)).const_mul_left (1 / 4 : ℝ)
      refine this.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
      simp only [lastDirectionWalk, lastDirectionP1, lastDirectionP2, stepR, stepT, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul, hc, if_true]
      ring
    · have e : (fun s : ℝ => lastDirectionWalk h s i j - (((1 / 4 : ℝ) • stepR) i j + s * lastDirectionP1 h i j +
          s ^ 2 / 2 * lastDirectionP2 h i j)) = fun _ => 0 := by
        funext s
        simp [lastDirectionWalk, lastDirectionP1, lastDirectionP2, stepR, stepT, hc]
      rw [e]
      exact Asymptotics.isBigO_zero _ _
  row := by
    rw [Matrix.smul_mulVec, stepR_mulVec_one, smul_smul]
    norm_num
  stat := by
    have e : piU = (1 / 80 : ℝ) • (1 : State → ℝ) := by
      funext i
      simp [piU]
    rw [e, Matrix.vecMul_smul, Matrix.smul_vecMul, one_vecMul_stepR, smul_smul, smul_smul]
    norm_num
  pos := fun _ => by simp [piU]
  total := sum_piU
  kerR := fun v hv => kernel_right v ((lastDirectionP0_mulVec v).mp hv)
  kerL := by
    intro w hw
    obtain ⟨c, hc⟩ := kernel_left w ((lastDirectionP0_vecMul w).mp hw)
    refine ⟨80 * c, ?_⟩
    rw [hc]
    funext i
    simp [piU]
    ring
  adj := by
    rw [adj_law_quarter]
    intro h0
    have := congrFun (congrFun h0 ((0 : Fin 16), (0 : Fin 5))) ((0 : Fin 16), (0 : Fin 5))
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.one_apply, mul_one, smul_eq_mul,
      Matrix.zero_apply] at this
    exact kappaLaw_pos.ne' this

/-- The Poisson solution in integers: `25 g = 16` on the last-step direction `h`, `−4` elsewhere. -/
def gLastDirectionZ (s : State) : ℤ := if s.2 = h then 16 else -4

/-- **The Poisson solution** `g = 16/25` on the states whose last-step direction is `h`, `−4/25` elsewhere. -/
noncomputable def gLastDirection (s : State) : ℝ := (gLastDirectionZ h s : ℝ) / 25

theorem gLastDirectionZ_pred_sum : ∀ (h : Fin 5) (s' : State),
    ∑ s ∈ predSet s', gLastDirectionZ h s = if s'.2 = h then -16 else 4 := by
  decide +kernel

theorem gLastDirectionZ_sum : ∀ h : Fin 5, ∑ s : State, gLastDirectionZ h s = 0 := by
  decide +kernel

theorem alongH_count : ∀ h : Fin 5,
    (Finset.univ.filter fun s : State => s.2 = h).card = 16 := by
  decide +kernel

theorem gLastDirection_pred_sum (s' : State) :
    ∑ s ∈ predSet s', gLastDirection h s = if s'.2 = h then -16 / 25 else 4 / 25 := by
  simp only [gLastDirection]
  rw [← Finset.sum_div, ← Int.cast_sum, gLastDirectionZ_pred_sum]
  split_ifs <;> norm_num

theorem lastDirectionP1_mulVec_one (s' : State) : (lastDirectionP1 h *ᵥ 1) s' = alongH h s' := by
  rw [lastDirectionP1, Matrix.smul_mulVec, Pi.smul_apply, stepT_mulVec_real]
  simp only [Pi.one_apply, mul_one, Finset.sum_const, card_predSet, smul_eq_mul, nsmul_eq_mul]
  norm_num
  ring

theorem lastDirectionP2_mulVec_one (s' : State) : (lastDirectionP2 h *ᵥ 1) s' = alongH h s' := by
  rw [lastDirectionP2, Matrix.smul_mulVec, Pi.smul_apply, stepT_mulVec_real]
  simp only [Pi.one_apply, mul_one, Finset.sum_const, card_predSet, smul_eq_mul, nsmul_eq_mul]
  simp only [alongH]
  split_ifs <;> norm_num

theorem lastDirectionP1_mulVec_g (s' : State) :
    (lastDirectionP1 h *ᵥ gLastDirection h) s' = if s'.2 = h then -4 / 25 else 0 := by
  rw [lastDirectionP1, Matrix.smul_mulVec, Pi.smul_apply, stepT_mulVec_real, ← Finset.mul_sum,
    gLastDirection_pred_sum]
  simp only [alongH, smul_eq_mul]
  split_ifs <;> norm_num

theorem sum_alongH : ∑ s' : State, alongH h s' = 16 := by
  simp only [alongH]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, alongH_count]
  norm_num

/-- `v = π P₁ 𝟏 = 1/5`. -/
theorem lastDirection_v : piU ⬝ᵥ (lastDirectionP1 h *ᵥ 1) = 1 / 5 := by
  simp only [dotProduct, piU, lastDirectionP1_mulVec_one]
  rw [← Finset.mul_sum, sum_alongH]
  norm_num

theorem lastDirection_poisson :
    (1 - (1 / 4 : ℝ) • stepR) *ᵥ gLastDirection h = lastDirectionP1 h *ᵥ 1 - (piU ⬝ᵥ (lastDirectionP1 h *ᵥ 1)) • 1 := by
  rw [lastDirection_v]
  funext s'
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Pi.smul_apply,
    stepR_mulVec, Pi.sub_apply, lastDirectionP1_mulVec_one, Pi.smul_apply]
  have hs : ∑ s ∈ predSet s', gLastDirection h s = if s'.2 = h then -16 / 25 else 4 / 25 :=
    gLastDirection_pred_sum h s'
  rw [hs]
  simp only [gLastDirection, gLastDirectionZ, alongH, smul_eq_mul, Pi.one_apply, mul_one]
  split_ifs <;> norm_num

theorem lastDirection_g_centred : piU ⬝ᵥ gLastDirection h = 0 := by
  simp only [dotProduct, piU, gLastDirection]
  rw [← Finset.mul_sum, ← Finset.sum_div, ← Int.cast_sum, gLastDirectionZ_sum]
  norm_num

/-- The second-order coefficient: `σ² = π P₂ 𝟏 + 2 π P₁ g − v² = 12/125`. -/
theorem lastDirection_sigma :
    piU ⬝ᵥ (lastDirectionP2 h *ᵥ 1) + 2 * (piU ⬝ᵥ (lastDirectionP1 h *ᵥ gLastDirection h)) -
      (piU ⬝ᵥ (lastDirectionP1 h *ᵥ 1)) ^ 2 = 12 / 125 := by
  rw [lastDirection_v]
  have h1 : piU ⬝ᵥ (lastDirectionP2 h *ᵥ 1) = 1 / 5 := by
    simp only [dotProduct, piU, lastDirectionP2_mulVec_one]
    rw [← Finset.mul_sum, sum_alongH]
    norm_num
  have h2 : piU ⬝ᵥ (lastDirectionP1 h *ᵥ gLastDirection h) = -4 / 125 := by
    simp only [dotProduct, piU, lastDirectionP1_mulVec_g]
    rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      alongH_count]
    norm_num
  rw [h1, h2]
  norm_num

/-- **Proposition 71 on the eighty states, the steps along the last-step direction:** the largest eigenvalue of
`(B/4) ∘ e^{s[along h]}` has `d/ds log ρ = 1/5` at `s = 0` (a fifth of the steps go along `h`) and
`log ρ(s) = s/5 + (s²/2)(12/125) + O(s³)`. -/
theorem lastDirection_velocity :
    (∀ᶠ s in 𝓝 (0 : ℝ), IsPerron (lastDirectionWalk h s) (perronRoot (lastDirectionWalk h) s)) ∧
    HasDerivAt (fun s => Real.log (perronRoot (lastDirectionWalk h) s)) (1 / 5) 0 ∧
    (fun s => Real.log (perronRoot (lastDirectionWalk h) s) - (s * (1 / 5) + s ^ 2 / 2 * (12 / 125)))
      =O[𝓝 0] (fun s => s ^ 3) := by
  have hW := lastDirectionWalk_weighted h
  obtain ⟨hd, hO⟩ := perron_log hW (gLastDirection h) (lastDirection_poisson h) (lastDirection_g_centred h)
  rw [lastDirection_sigma, lastDirection_v] at hO
  rw [lastDirection_v] at hd
  exact ⟨perronRoot_spec hW, hd, hO⟩

/-- **The second derivative is the asymptotic variance:** the second-order coefficient `12/125` of
`lastDirection_velocity` is the sum of the covariance series `Σ_{k ∈ ℤ} Cov(X₀, X_k)` of the steps along `h`
(`lastDirection_spread`, Proposition 71 in `Zero.lean`). -/
theorem lastDirection_variance_is_spread :
    piU ⬝ᵥ (lastDirectionP2 h *ᵥ 1) + 2 * (piU ⬝ᵥ (lastDirectionP1 h *ᵥ gLastDirection h)) -
      (piU ⬝ᵥ (lastDirectionP1 h *ᵥ 1)) ^ 2 = 12 / 125 ∧
    HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) * ((4 / 25) * (-1 / 4) ^ k))
      (12 / 125) :=
  ⟨lastDirection_sigma h, lastDirection_spread⟩

end LastDirection

/-! ## The available transitions of a last-step direction, the transitions weighed by `L(Ω) + [along h]` (Proposition 78) -/

section AvailableTransitions

variable (h : Fin 5)

/-- The weight of a transition: `L(Ω) + [along h] = 6 + [along h]` (`transition_weight` in `Inventory.lean`). -/
noncomputable def transitionX (s' : State) : ℝ := 6 + alongH h s'

/-- Watching a matrix of steps on the available transitions: `M_AA/4 + B_AD M_DA/16 + B_AD B_DD M_DA/64`; the steps
out of the available transitions (the transitions) carry `M`, the hidden steps carry `B`. -/
noncomputable def watchOf (M : Matrix State State ℝ) :
    Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  (1 / 4 : ℝ) • M.toBlock (InAvailableTransitions h) (InAvailableTransitions h) +
    (1 / 16 : ℝ) • (bAD h * M.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)) +
    (1 / 64 : ℝ) • (bAD h * bDD h * M.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h))

theorem watchOf_stepR : watchOf h stepR = watchedR h := rfl

/-- **The walk watched on the available transitions with the weight `e^{sX}` on each transition.** -/
noncomputable def watchedS (s : ℝ) : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  watchOf h (stepT (fun _ s' => Real.exp (s * transitionX h s')))

/-- Its derivatives at `s = 0`: the transitions weighed by `X^k`. -/
noncomputable def watchedK (k : ℕ) : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  watchOf h (stepT (fun _ s' => transitionX h s' ^ k))

theorem watchOf_apply (M : Matrix State State ℝ) (a' a : {s // InAvailableTransitions h s}) :
    watchOf h M a' a = (1 / 4) * M a' a + (1 / 16) * ∑ d : {s // ¬InAvailableTransitions h s},
      bAD h a' d * M d a + (1 / 64) * ∑ d : {s // ¬InAvailableTransitions h s}, (bAD h * bDD h) a' d * M d a := by
  simp only [watchOf, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    toBlock_apply]

theorem watchOf_entry_isBigO (R : ℝ → Matrix State State ℝ)
    (hR : ∀ i j, (fun s => R s i j) =O[𝓝 0] (fun s : ℝ => s ^ 3)) (a' a : {s // InAvailableTransitions h s}) :
    (fun s => watchOf h (R s) a' a) =O[𝓝 0] (fun s : ℝ => s ^ 3) := by
  simp only [watchOf_apply]
  refine (((hR a' a).const_mul_left _).add ?_).add ?_
  · exact (Asymptotics.IsBigO.fun_sum fun (d : {s // ¬InAvailableTransitions h s}) _ =>
      (hR (d : State) a).const_mul_left (bAD h a' d)).const_mul_left _
  · exact (Asymptotics.IsBigO.fun_sum fun (d : {s // ¬InAvailableTransitions h s}) _ =>
      (hR (d : State) a).const_mul_left ((bAD h * bDD h) a' d)).const_mul_left _

theorem toBlock_add' (M N : Matrix State State ℝ) (p q : State → Prop) :
    (M + N).toBlock p q = M.toBlock p q + N.toBlock p q := by
  ext i j
  simp [toBlock_apply]

theorem toBlock_smul' (c : ℝ) (M : Matrix State State ℝ) (p q : State → Prop) :
    (c • M).toBlock p q = c • M.toBlock p q := by
  ext i j
  simp [toBlock_apply]

theorem watchOf_add (M N : Matrix State State ℝ) : watchOf h (M + N) = watchOf h M + watchOf h N := by
  simp only [watchOf, toBlock_add', Matrix.mul_add, smul_add]
  abel

theorem watchOf_smul (c : ℝ) (M : Matrix State State ℝ) : watchOf h (c • M) = c • watchOf h M := by
  simp only [watchOf, toBlock_smul', Matrix.mul_smul, smul_add, smul_comm c]

theorem watchOf_lin (M N0 N1 N2 R : Matrix State State ℝ) (b1 b2 : ℝ)
    (hM : ∀ i j, M i j = N0 i j + b1 * N1 i j + b2 * N2 i j + R i j) (a' a : {s // InAvailableTransitions h s}) :
    watchOf h M a' a =
      watchOf h N0 a' a + b1 * watchOf h N1 a' a + b2 * watchOf h N2 a' a + watchOf h R a' a := by
  have e : M = N0 + b1 • N1 + b2 • N2 + R := by
    ext i j
    simp [hM i j]
  rw [e, watchOf_add, watchOf_add, watchOf_add, watchOf_smul, watchOf_smul]
  simp

theorem glue_one : glue h (1 : {s // InAvailableTransitions h s} → ℝ) (1 : {s // ¬InAvailableTransitions h s} → ℝ) = 1 := by
  funext s
  simp only [glue, Pi.one_apply]
  split_ifs <;> rfl

theorem bAA_one : bAA h *ᵥ 1 = (4 : ℝ) • 1 - bAD h *ᵥ 1 := by
  funext a
  have := stepR_glue_A h 1 1 a
  rw [glue_one, stepR_mulVec_one] at this
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
  linarith

theorem bDA_one : bDA h *ᵥ 1 = (4 : ℝ) • 1 - bDD h *ᵥ 1 := by
  funext d
  have := stepR_glue_D h 1 1 d
  rw [glue_one, stepR_mulVec_one] at this
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
  linarith

theorem one_bAA : (1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAA h = (4 : ℝ) • 1 - 1 ᵥ* bDA h := by
  funext a
  have := glue_vecMul_A h 1 1 a
  rw [glue_one, one_vecMul_stepR] at this
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
  linarith

theorem one_bAD : (1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h = (4 : ℝ) • 1 - 1 ᵥ* bDD h := by
  funext d
  have := glue_vecMul_D h 1 1 d
  rw [glue_one, one_vecMul_stepR] at this
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
  linarith

/-- **The watched walk is stochastic:** `W 𝟏 = 𝟏`. -/
theorem watchedR_rows : watchedR h *ᵥ 1 = 1 := by
  have hBB : ∀ v, bDD h *ᵥ (bDD h *ᵥ v) = 0 := by
    intro v
    rw [Matrix.mulVec_mulVec, bDD_sq, Matrix.zero_mulVec]
  rw [watchedR]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, bDA_one, bAA_one,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hBB, Matrix.mulVec_zero, sub_zero]
  module

/-- **The uniform law is stationary for the watched walk:** `𝟏ᵀ W = 𝟏ᵀ`. -/
theorem watchedR_cols : (1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* watchedR h = 1 := by
  have hBB : ∀ v : {s // ¬InAvailableTransitions h s} → ℝ, v ᵥ* bDD h ᵥ* bDD h = 0 := by
    intro v
    rw [Matrix.vecMul_vecMul, bDD_sq, Matrix.vecMul_zero]
  rw [watchedR]
  simp only [Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, one_bAD, one_bAA,
    Matrix.sub_vecMul, Matrix.smul_vecMul, hBB, sub_zero]
  module

/-- The uniform law on the seventy-four. -/
noncomputable def piA : {s // InAvailableTransitions h s} → ℝ := fun _ => 1 / 74

theorem card_availableTransitions : Fintype.card {s // InAvailableTransitions h s} = 74 := by
  rw [Fintype.card_subtype]
  have := card_excursionStates h
  simpa [excursionStates, InAvailableTransitions] using this

theorem piA_eq : piA h = (1 / 74 : ℝ) • (1 : {s // InAvailableTransitions h s} → ℝ) := by
  funext a
  simp [piA]

theorem availableTransitions_witness_all : ∀ h : Fin 5,
    InAvailableTransitions h (transition (if h = 0 then 1 else 0) 0, (if h = 0 then 1 else 0)) := by
  decide

theorem availableTransitions_witness : InAvailableTransitions h (transition (if h = 0 then 1 else 0) 0, (if h = 0 then 1 else 0)) :=
  availableTransitions_witness_all h

theorem adj_watched_ne : (1 - watchedR h).adjugate ≠ 0 := by
  obtain ⟨κ, hκ⟩ := adj_watched_exists h
  have hJ := availableTransitionsOp_hasDerivAt h (1 / 4)
  rw [availableTransitionsOp_quarter, hκ, trace_smul_vecMulVec_mul] at hJ
  have hD : HasDerivAt (fun v => (availableTransitionsOp h v).det) (-96 * (15 / 16 : ℝ) ^ 24) (1 / 4) := by
    have e : (fun v => (availableTransitionsOp h v).det) = Dplus := funext (det_availableTransitionsOp h)
    rw [e]
    exact Dplus_hasDerivAt
  have := hJ.unique hD
  intro h0
  rw [hκ] at h0
  have hκ0 : κ = 0 := by
    have := congrFun (congrFun h0 ⟨_, availableTransitions_witness h⟩) ⟨_, availableTransitions_witness h⟩
    simpa using this
  rw [hκ0, zero_mul] at this
  norm_num at this

end AvailableTransitions

/-! ### The watched walk with weighed transitions is a weighted walk -/

section AvailableTransitions2

variable (h : Fin 5)

theorem transition_taylor_entry (s : ℝ) (i j : State) :
    stepT (fun _ s' => Real.exp (s * transitionX h s')) i j =
      stepR i j + s * stepT (fun _ s' => transitionX h s' ^ 1) i j +
        s ^ 2 / 2 * stepT (fun _ s' => transitionX h s' ^ 2) i j +
        stepT (fun _ s' => Real.exp (s * transitionX h s') -
          (1 + s * transitionX h s' + s ^ 2 / 2 * transitionX h s' ^ 2)) i j := by
  simp only [stepR, stepT, Matrix.of_apply]
  split_ifs <;> ring

theorem transition_remainder (i j : State) :
    (fun s : ℝ => stepT (fun _ s' => Real.exp (s * transitionX h s') -
      (1 + s * transitionX h s' + s ^ 2 / 2 * transitionX h s' ^ 2)) i j) =O[𝓝 0] (fun s : ℝ => s ^ 3) := by
  by_cases hc : Continues j i
  · have := exp_taylor2 (transitionX h i)
    refine this.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp only [stepT, Matrix.of_apply, hc, if_true]
  · have e : (fun s : ℝ => stepT (fun _ s' => Real.exp (s * transitionX h s') -
        (1 + s * transitionX h s' + s ^ 2 / 2 * transitionX h s' ^ 2)) i j) = fun _ => 0 := by
      funext s
      simp [stepT, hc]
    rw [e]
    exact Asymptotics.isBigO_zero _ _

/-- **The walk watched on the available transitions, with the weight `e^{sX}` on each transition, is a weighted walk.** -/
theorem watched_weighted :
    WeightedWalk (watchedS h) (watchedR h) (watchedK h 1) (watchedK h 2) (piA h) where
  nonneg := by
    intro s i j
    simp only [watchedS, watchOf_apply]
    have hM : ∀ x y : State, 0 ≤ stepT (fun _ s' => Real.exp (s * transitionX h s')) x y := by
      intro x y
      simp only [stepT, Matrix.of_apply]
      split_ifs
      · positivity
      · norm_num
    have hB : ∀ x y : State, 0 ≤ stepR x y := by
      intro x y
      simp only [stepR, stepT, Matrix.of_apply]
      split_ifs <;> norm_num
    have hBD : ∀ x : {s // InAvailableTransitions h s}, ∀ y : {s // ¬InAvailableTransitions h s}, 0 ≤ (bAD h * bDD h) x y := by
      intro x y
      simp only [Matrix.mul_apply, toBlock_apply, bDD, blockDD]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hB _ _) (by
        simp only [stepT, Matrix.of_apply]
        split_ifs <;> norm_num)
    refine add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hM _ _)) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun d _ => mul_nonneg (hB _ _) (hM _ _)))) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun d _ => mul_nonneg (hBD _ _) (hM _ _)))
  taylor := by
    intro a' a
    have hlin := fun s : ℝ => watchOf_lin h (stepT (fun _ s' => Real.exp (s * transitionX h s')))
      stepR (stepT (fun _ s' => transitionX h s' ^ 1)) (stepT (fun _ s' => transitionX h s' ^ 2))
      (stepT (fun _ s' => Real.exp (s * transitionX h s') -
        (1 + s * transitionX h s' + s ^ 2 / 2 * transitionX h s' ^ 2))) s (s ^ 2 / 2)
      (transition_taylor_entry h s) a' a
    have hO := watchOf_entry_isBigO h (fun s : ℝ => stepT (fun _ s' => Real.exp (s * transitionX h s') -
      (1 + s * transitionX h s' + s ^ 2 / 2 * transitionX h s' ^ 2))) (transition_remainder h) a' a
    refine hO.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp only [watchedS, watchedK, ← watchOf_stepR]
    rw [hlin s]
    ring
  row := watchedR_rows h
  stat := by
    rw [piA_eq, Matrix.smul_vecMul, watchedR_cols]
  pos := fun _ => by simp [piA]
  total := by
    simp only [piA, Finset.sum_const, Finset.card_univ, card_availableTransitions, nsmul_eq_mul]
    norm_num
  kerR := fun v hv => watched_kernel_right h v hv
  kerL := by
    intro w hw
    obtain ⟨c, hc⟩ := watched_kernel_left h w hw
    refine ⟨74 * c, ?_⟩
    rw [hc, piA_eq, smul_smul]
    congr 1
    ring
  adj := adj_watched_ne h

/-! ### The sum over the transitions -/

/-- The weight of a transition in integers. -/
def transitionNat (s' : State) : ℕ := 6 + if s'.2 = h then 1 else 0

theorem transitionX_eq (s' : State) : transitionX h s' = (transitionNat h s' : ℝ) := by
  simp only [transitionX, alongH, transitionNat]
  split_ifs <;> norm_num

/-- The available directed edges a state continues. -/
def predA (s' : State) : ℕ := (Finset.univ.filter fun s => InAvailableTransitions h s ∧ Continues s s').card

/-- The available directed edges that continue a state. -/
def succA (s : State) : ℕ := (Finset.univ.filter fun s' => InAvailableTransitions h s' ∧ Continues s s').card

/-- The available directed edges reached from a closed state by one hidden step and one more. -/
def succDA (d : State) : ℕ :=
  ∑ d' ∈ Finset.univ.filter (fun d' => ¬InAvailableTransitions h d' ∧ Continues d d'), succA h d'

theorem sum_availableTransitions (F : State → ℝ) :
    ∑ a : {s // InAvailableTransitions h s}, F a = ∑ s ∈ Finset.univ.filter (fun s => InAvailableTransitions h s), F s :=
  (Finset.sum_subtype _ (by simp) F).symm

theorem sum_closed (F : State → ℝ) :
    ∑ d : {s // ¬InAvailableTransitions h s}, F d = ∑ s ∈ Finset.univ.filter (fun s => ¬InAvailableTransitions h s), F s :=
  (Finset.sum_subtype _ (by simp) F).symm

theorem count_real (P : State → Prop) [DecidablePred P] (Q : State → Prop) [DecidablePred Q] :
    ∑ s ∈ Finset.univ.filter P, (if Q s then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun s => P s ∧ Q s).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem transitionAA_one (k : ℕ) (a' : {s // InAvailableTransitions h s}) :
    ((stepT (fun _ s' => transitionX h s' ^ k)).toBlock (InAvailableTransitions h) (InAvailableTransitions h) *ᵥ 1) a' =
      transitionX h a' ^ k * (predA h a' : ℝ) := by
  simp only [Matrix.mulVec, dotProduct, toBlock_apply, stepT, Matrix.of_apply, Pi.one_apply,
    mul_one]
  rw [sum_availableTransitions h (fun s => if Continues s a' then transitionX h a' ^ k else 0)]
  rw [show (fun s => if Continues s a' then transitionX h a' ^ k else 0) =
    fun s => transitionX h a' ^ k * (if Continues s a' then 1 else 0) by
      funext s
      split_ifs <;> simp]
  rw [← Finset.mul_sum, count_real]
  rfl

theorem transitionDA_one (k : ℕ) (d : {s // ¬InAvailableTransitions h s}) :
    ((stepT (fun _ s' => transitionX h s' ^ k)).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1) d =
      transitionX h d ^ k * (predA h d : ℝ) := by
  simp only [Matrix.mulVec, dotProduct, toBlock_apply, stepT, Matrix.of_apply, Pi.one_apply,
    mul_one]
  rw [sum_availableTransitions h (fun s => if Continues s d then transitionX h d ^ k else 0)]
  rw [show (fun s => if Continues s d then transitionX h d ^ k else 0) =
    fun s => transitionX h d ^ k * (if Continues s d then 1 else 0) by
      funext s
      split_ifs <;> simp]
  rw [← Finset.mul_sum, count_real]
  rfl

theorem one_bAD_eq (d : {s // ¬InAvailableTransitions h s}) :
    ((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h) d = (succA h d : ℝ) := by
  simp only [Matrix.vecMul, dotProduct, toBlock_apply, stepR, stepT, Matrix.of_apply,
    Pi.one_apply, one_mul]
  rw [sum_availableTransitions h (fun s => if Continues (d : State) s then (1 : ℝ) else 0), count_real]
  rfl

theorem one_bAD_bDD_eq (d : {s // ¬InAvailableTransitions h s}) :
    ((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h ᵥ* bDD h) d = (succDA h d : ℝ) := by
  rw [Matrix.vecMul, dotProduct]
  simp only [one_bAD_eq, bDD, blockDD, toBlock_apply, stepT, Matrix.of_apply, mul_ite, mul_one,
    mul_zero]
  rw [sum_closed h (fun s => if Continues (d : State) s then (succA h s : ℝ) else 0)]
  simp only [succDA]
  rw [← Finset.sum_filter, Finset.filter_filter]
  push_cast
  rfl

theorem watchOf_dot (M : Matrix State State ℝ) :
    (1 : {s // InAvailableTransitions h s} → ℝ) ⬝ᵥ (watchOf h M *ᵥ 1) =
      (1 / 4) * ((1 : {s // InAvailableTransitions h s} → ℝ) ⬝ᵥ
        (M.toBlock (InAvailableTransitions h) (InAvailableTransitions h) *ᵥ 1)) +
      (1 / 16) * (((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h) ⬝ᵥ
        (M.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1)) +
      (1 / 64) * (((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h ᵥ* bDD h) ⬝ᵥ
        (M.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1)) := by
  simp only [watchOf, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]

/-- The three transition sums: `Σ_{A→A} X = 1712`, `Σ_d (succ in A)(Σ_{A→d} X) = 400`,
`Σ_d (succ in A after one hidden step)(Σ_{A→d} X) = 384`. -/
theorem transition_counts : ∀ h : Fin 5,
    ∑ s ∈ Finset.univ.filter (fun s => InAvailableTransitions h s), transitionNat h s * predA h s = 1712 ∧
    ∑ s ∈ Finset.univ.filter (fun s => ¬InAvailableTransitions h s), succA h s * (transitionNat h s * predA h s) = 400 ∧
    ∑ s ∈ Finset.univ.filter (fun s => ¬InAvailableTransitions h s), succDA h s * (transitionNat h s * predA h s) =
      384 := by
  decide +kernel

/-- **`𝟏ᵀ W₁ 𝟏 = 1712/4 + 400/16 + 384/64 = 459`: the transitions, each weighed by `L(Ω) + [along h]`, sum
to `1836` over the available transitions, a quarter of it per state's continuation.** -/
theorem watched_transition_sum : (1 : {s // InAvailableTransitions h s} → ℝ) ⬝ᵥ (watchedK h 1 *ᵥ 1) = 459 := by
  rw [watchedK, watchOf_dot]
  obtain ⟨c1, c2, c3⟩ := transition_counts h
  have e1 : (1 : {s // InAvailableTransitions h s} → ℝ) ⬝ᵥ
      ((stepT (fun _ s' => transitionX h s' ^ 1)).toBlock (InAvailableTransitions h) (InAvailableTransitions h) *ᵥ 1) = 1712 := by
    simp only [dotProduct, Pi.one_apply, one_mul, transitionAA_one]
    rw [sum_availableTransitions h (fun s => transitionX h s ^ 1 * (predA h s : ℝ))]
    simp only [pow_one, transitionX_eq]
    exact_mod_cast c1
  have e2 : ((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h) ⬝ᵥ
      ((stepT (fun _ s' => transitionX h s' ^ 1)).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1) =
        400 := by
    simp only [dotProduct, one_bAD_eq, transitionDA_one]
    rw [sum_closed h (fun s => (succA h s : ℝ) * (transitionX h s ^ 1 * (predA h s : ℝ)))]
    simp only [pow_one, transitionX_eq]
    exact_mod_cast c2
  have e3 : ((1 : {s // InAvailableTransitions h s} → ℝ) ᵥ* bAD h ᵥ* bDD h) ⬝ᵥ
      ((stepT (fun _ s' => transitionX h s' ^ 1)).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1) =
        384 := by
    simp only [dotProduct, one_bAD_bDD_eq, transitionDA_one]
    rw [sum_closed h (fun s => (succDA h s : ℝ) * (transitionX h s ^ 1 * (predA h s : ℝ)))]
    simp only [pow_one, transitionX_eq]
    exact_mod_cast c3
  rw [e1, e2, e3]
  norm_num

/-- **The velocity of the transition weight on the watched walk:** `π W₁ 𝟏 = 459/74 = 1836/296`. -/
theorem watched_v : piA h ⬝ᵥ (watchedK h 1 *ᵥ 1) = 1836 / 296 := by
  rw [piA_eq, smul_dotProduct, watched_transition_sum, smul_eq_mul]
  norm_num

/-- **Proposition 78.** On the walk watched on the available transitions of `h`, with the weight `e^{sX}` on each
transition, `X = L(Ω) + [along h]`, the largest eigenvalue `ρ_W(s)` exists near `s = 0` with positive
eigenvectors, **`d/ds log ρ_W(s) = 1836/296` exactly at `s = 0`**, and
`log ρ_W(s) = (1836/296)s + (s²/2)σ²_W + O(s³)` with `σ²_W = π W₂ 𝟏 + 2 π W₁ g − (1836/296)²`
for the Poisson solution `g` (which exists by `solvable`). -/
theorem inventory_velocity :
    (∀ᶠ s in 𝓝 (0 : ℝ), IsPerron (watchedS h s) (perronRoot (watchedS h) s)) ∧
    HasDerivAt (fun s => Real.log (perronRoot (watchedS h) s)) (1836 / 296) 0 ∧
    ∃ g : {s // InAvailableTransitions h s} → ℝ,
      (fun s => Real.log (perronRoot (watchedS h) s) - (s * (1836 / 296) + s ^ 2 / 2 *
        (piA h ⬝ᵥ (watchedK h 2 *ᵥ 1) + 2 * (piA h ⬝ᵥ (watchedK h 1 *ᵥ g)) - (1836 / 296) ^ 2)))
        =O[𝓝 0] (fun s => s ^ 3) := by
  have hW := watched_weighted h
  haveI := hW.nonempty
  have hπne : piA h ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨_, availableTransitions_witness h⟩
    simp [piA] at this
  have hπ1 : piA h ⬝ᵥ (1 : {s // InAvailableTransitions h s} → ℝ) = 1 := by
    simp only [dotProduct, Pi.one_apply, mul_one]
    exact hW.total
  obtain ⟨g0, hg0⟩ := solvable (watchedR h) (piA h) hπne hW.stat hW.row hW.kerR
    (watchedK h 1 *ᵥ 1 - (piA h ⬝ᵥ (watchedK h 1 *ᵥ 1)) • 1) (by
      rw [dotProduct_sub, dotProduct_smul, hπ1, smul_eq_mul, mul_one, sub_self])
  set g := g0 - (piA h ⬝ᵥ g0) • (1 : {s // InAvailableTransitions h s} → ℝ) with hgdef
  have hg : (1 - watchedR h) *ᵥ g = watchedK h 1 *ᵥ 1 - (piA h ⬝ᵥ (watchedK h 1 *ᵥ 1)) • 1 := by
    rw [hgdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hg0]
    have : (1 - watchedR h) *ᵥ (1 : {s // InAvailableTransitions h s} → ℝ) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hW.row, sub_self]
    rw [this, smul_zero, sub_zero]
  have hπg : piA h ⬝ᵥ g = 0 := by
    rw [hgdef, dotProduct_sub, dotProduct_smul, hπ1, smul_eq_mul, mul_one, sub_self]
  obtain ⟨hd, hO⟩ := perron_log hW g hg hπg
  rw [watched_v] at hd hO
  exact ⟨perronRoot_spec hW, hd, g, hO⟩

end AvailableTransitions2

end Comparison

end
