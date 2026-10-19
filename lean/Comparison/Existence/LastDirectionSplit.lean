module

public import Comparison.Existence.Walk

/-!
# Book XI. The ten rotations split at the last-step direction (Proposition 61)

The ten rotations are the `γ_aγ_b`;
at a last-step direction `h` they split into the six `γ_aγ_b` (`a, b ≠ h`), the rotations `so(4)` that keep the last-step direction,
and the four `γ_hγ_a`, written `e/ℓ`.

* `lc5`: the Levi-Civita symbol of five indices (zero when an index repeats).
* `trace_five`: **`tr(γ_aγ_bγ_cγ_dγ_e) = 4 ε_{abcde}`** for all five indices (all `5⁵` cases,
  checked over the Gaussian integers).
* `lastDirection_square`: `(γ_hγ_a)(γ_hγ_b) = −γ_aγ_b` for `a, b ≠ h`: the square of the four lies in the six;
  `lastDirection_commutator`: `[γ_hγ_a, γ_hγ_b] = −2γ_aγ_b`: **`[ℝ⁴, ℝ⁴] ⊆ so(4)`**;
  `keep_move`: `[γ_aγ_b, γ_hγ_c]` is again of the form `γ_h(·)`.
* `lastDirectionCurv h F T = ¼ Σ_{a,b≠h} F_ab γ_aγ_b + ½ Σ_{a≠h} T_a γ_hγ_a`; `trace_lastDirection_curv`:
  **`tr(γ_h 𝓕𝓕) = ¼ Σ ε_{habcd} F_ab F_cd`**: only the part in the six survives.
* `mm_expand`: with `F = R − E/ℓ²`, `Σ εFF = Σ εRR − (2/ℓ²) Σ εRE + (1/ℓ⁴) Σ εEE`;
  `lambda_from_ratio`: matching `ε(Ree − (Λ/6)eeee)` gives **`Λ = 3/ℓ²`**.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Finset

/-- **The Levi-Civita symbol** of five indices: the sign of the permutation, `0` on a repeat. -/
def lc5 (a b c d e : Fin 5) : ℤ :=
  if Function.Injective ![a, b, c, d, e] then
    (-1) ^ (Finset.univ.filter fun p : Fin 5 × Fin 5 =>
      p.1 < p.2 ∧ ![a, b, c, d, e] p.2 < ![a, b, c, d, e] p.1).card
  else 0

theorem trace_fiveZ : ∀ a b c d e : Fin 5,
    ((γZ a * γZ b * γZ c * γZ d * γZ e).trace) = 4 * (lc5 a b c d e : GaussianInt) := by
  decide +kernel

/-- **`tr(γ_aγ_bγ_cγ_dγ_e) = 4 ε_{abcde}`.** -/
theorem trace_five (a b c d e : Fin 5) :
    (γ a * γ b * γ c * γ d * γ e).trace = 4 * (lc5 a b c d e : ℂ) := by
  have h := congrArg GaussianInt.toComplex (trace_fiveZ a b c d e)
  rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, γZ_map,
    γZ_map, γZ_map, γZ_map, γZ_map, map_mul, map_intCast] at h
  rw [h, map_ofNat]

theorem lc5_lastDirection_repeat : ∀ h a b c : Fin 5,
    lc5 h a b h c = 0 ∧ lc5 h h a b c = 0 ∧ lc5 h h a h b = 0 := by
  decide

theorem lc5_pair_swap : ∀ h a b c d : Fin 5, lc5 h a b c d = lc5 h c d a b := by
  decide

theorem lc5_identity : lc5 0 1 2 3 4 = 1 := by decide

/-- **The square of the four lies in the six:** `(γ_hγ_a)(γ_hγ_b) = −γ_aγ_b` for `a, b ≠ h`. -/
theorem lastDirection_square {h a b : Fin 5} (ha : a ≠ h) (_hb : b ≠ h) :
    (γ h * γ a) * (γ h * γ b) = -(γ a * γ b) := by
  calc γ h * γ a * (γ h * γ b) = γ h * (γ a * γ h) * γ b := by noncomm_ring
    _ = γ h * (-(γ h * γ a)) * γ b := by rw [γ_anticomm ha]
    _ = -((γ h * γ h) * γ a * γ b) := by noncomm_ring
    _ = -(γ a * γ b) := by rw [γ_mul_self, Matrix.one_mul]

/-- **`[ℝ⁴, ℝ⁴] ⊆ so(4)`:** `[γ_hγ_a, γ_hγ_b] = −2γ_aγ_b`. -/
theorem lastDirection_commutator {h a b : Fin 5} (ha : a ≠ h) (hb : b ≠ h) (hab : a ≠ b) :
    (γ h * γ a) * (γ h * γ b) - (γ h * γ b) * (γ h * γ a) = (-2 : ℂ) • (γ a * γ b) := by
  rw [lastDirection_square ha hb, lastDirection_square hb ha, γ_anticomm (Ne.symm hab)]
  rw [neg_neg, neg_smul, two_smul]
  abel

/-- `so(4)` moves the four into the four: `[γ_aγ_b, γ_hγ_c] = γ_h[γ_aγ_b, γ_c]`. -/
theorem keep_move {h a b c : Fin 5} (ha : a ≠ h) (hb : b ≠ h) :
    (γ a * γ b) * (γ h * γ c) - (γ h * γ c) * (γ a * γ b) =
      γ h * ((γ a * γ b) * γ c - γ c * (γ a * γ b)) := by
  have e : γ a * γ b * γ h = γ h * (γ a * γ b) := by
    calc γ a * γ b * γ h = γ a * (γ b * γ h) := by noncomm_ring
      _ = γ a * (-(γ h * γ b)) := by rw [γ_anticomm hb]
      _ = -((γ a * γ h) * γ b) := by noncomm_ring
      _ = -((-(γ h * γ a)) * γ b) := by rw [γ_anticomm ha]
      _ = γ h * (γ a * γ b) := by noncomm_ring
  calc γ a * γ b * (γ h * γ c) - γ h * γ c * (γ a * γ b)
      = (γ a * γ b * γ h) * γ c - γ h * γ c * (γ a * γ b) := by noncomm_ring
    _ = γ h * ((γ a * γ b) * γ c - γ c * (γ a * γ b)) := by rw [e]; noncomm_ring

/-! ## The curvature of the ten at the last-step direction -/

/-- `𝓕 = ¼ Σ_{a,b≠h} F_ab γ_aγ_b + ½ Σ_{a≠h} T_a γ_hγ_a`. -/
noncomputable def lastDirectionCurv (h : Fin 5) (F : Fin 5 → Fin 5 → ℂ) (T : Fin 5 → ℂ) :
    Matrix Four Four ℂ :=
  ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ((1 / 4 : ℂ) * F p.1 p.2) • (γ p.1 * γ p.2) +
    ∑ a ∈ univ.erase h, ((1 / 2 : ℂ) * T a) • (γ h * γ a)

theorem trace_bilin {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℂ) (y : κ → ℂ)
    (G : Matrix Four Four ℂ) (A : ι → Matrix Four Four ℂ) (B : κ → Matrix Four Four ℂ) :
    Matrix.trace (G * (∑ i ∈ s, x i • A i) * (∑ j ∈ t, y j • B j)) =
      ∑ i ∈ s, ∑ j ∈ t, x i * y j * Matrix.trace (G * A i * B j) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Only the six survive in the trace against the last-step direction:**
`tr(γ_h 𝓕𝓕) = ¼ Σ_{(a,b),(c,d)} ε_{habcd} F_ab F_cd`. -/
theorem trace_lastDirection_curv (h : Fin 5) (F : Fin 5 → Fin 5 → ℂ) (T : Fin 5 → ℂ) :
    (γ h * lastDirectionCurv h F T * lastDirectionCurv h F T).trace =
      (1 / 4 : ℂ) * ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
        (lc5 h p.1 p.2 q.1 q.2 : ℂ) * F p.1 p.2 * F q.1 q.2 := by
  simp only [lastDirectionCurv, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  rw [trace_bilin, trace_bilin, trace_bilin, trace_bilin]
  have e1 : ∀ a b c d : Fin 5, (γ h * (γ a * γ b) * (γ c * γ d)).trace = 4 * (lc5 h a b c d : ℂ) :=
    fun a b c d => by rw [← trace_five]; congr 1; noncomm_ring
  have r1 : ∀ a b c : Fin 5, lc5 h a b h c = 0 := fun a b c => (lc5_lastDirection_repeat h a b c).1
  have r2 : ∀ a b c : Fin 5, lc5 h h a b c = 0 := fun a b c => (lc5_lastDirection_repeat h a b c).2.1
  simp only [e1, r1, r2, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The MacDowell–Mansouri expansion:** with `F = R − E/ℓ²`,
`Σ εFF = Σ εRR − (2/ℓ²) Σ εRE + (1/ℓ⁴) Σ εEE` (the sums over pairs of pairs at the last-step direction). -/
theorem mm_expand (h : Fin 5) (R E : Fin 5 → Fin 5 → ℂ) (ℓ : ℂ) :
    ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
        (lc5 h p.1 p.2 q.1 q.2 : ℂ) * (R p.1 p.2 - E p.1 p.2 / ℓ ^ 2) *
          (R q.1 q.2 - E q.1 q.2 / ℓ ^ 2) =
      ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h), ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h),
          (lc5 h p.1 p.2 q.1 q.2 : ℂ) * R p.1 p.2 * R q.1 q.2 -
        2 / ℓ ^ 2 * ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h),
          ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h), (lc5 h p.1 p.2 q.1 q.2 : ℂ) * R p.1 p.2 * E q.1 q.2 +
        1 / ℓ ^ 4 * ∑ p ∈ (univ.erase h) ×ˢ (univ.erase h),
          ∑ q ∈ (univ.erase h) ×ˢ (univ.erase h), (lc5 h p.1 p.2 q.1 q.2 : ℂ) * E p.1 p.2 * E q.1 q.2 := by
  set S := (univ.erase h) ×ˢ (univ.erase h)
  -- the cross term with `E` first equals the one with `R` first, by the pair swap
  have hswap : ∑ p ∈ S, ∑ q ∈ S, (lc5 h p.1 p.2 q.1 q.2 : ℂ) * E p.1 p.2 * R q.1 q.2 =
      ∑ p ∈ S, ∑ q ∈ S, (lc5 h p.1 p.2 q.1 q.2 : ℂ) * R p.1 p.2 * E q.1 q.2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [lc5_pair_swap h q.1 q.2 p.1 p.2]
    ring
  have hsplit : ∀ p q : Fin 5 × Fin 5, (lc5 h p.1 p.2 q.1 q.2 : ℂ) *
      (R p.1 p.2 - E p.1 p.2 / ℓ ^ 2) * (R q.1 q.2 - E q.1 q.2 / ℓ ^ 2) =
      (lc5 h p.1 p.2 q.1 q.2 : ℂ) * R p.1 p.2 * R q.1 q.2 -
        1 / ℓ ^ 2 * ((lc5 h p.1 p.2 q.1 q.2 : ℂ) * R p.1 p.2 * E q.1 q.2) -
        1 / ℓ ^ 2 * ((lc5 h p.1 p.2 q.1 q.2 : ℂ) * E p.1 p.2 * R q.1 q.2) +
        1 / ℓ ^ 4 * ((lc5 h p.1 p.2 q.1 q.2 : ℂ) * E p.1 p.2 * E q.1 q.2) := by
    intro p q
    ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hswap]
  ring

/-- **`Λ = 3/ℓ²`:** the ratio of the volume term to the curvature-times-area term,
`(1/ℓ⁴)/(−2/ℓ²)`, is `−Λ/6` exactly when `Λ = 3/ℓ²`. -/
theorem lambda_from_ratio (ℓ Λ : ℝ) (hℓ : ℓ ≠ 0) :
    (1 / ℓ ^ 4) / (-(2 / ℓ ^ 2)) = -(Λ / 6) ↔ Λ = 3 / ℓ ^ 2 := by
  have h2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have h4 : ℓ ^ 4 ≠ 0 := pow_ne_zero 4 hℓ
  constructor
  · intro h
    field_simp at h
    field_simp
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring

/-- `so(5) = so(4) ⊕ ℝ⁴`: ten rotations, six keeping the last-step direction and four moving it. -/
theorem ten_split : (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2).card = 10 ∧
    (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ p.1 ≠ 0 ∧ p.2 ≠ 0).card = 6 ∧
    (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ (p.1 = 0 ∨ p.2 = 0)).card = 4 := by
  decide

end Comparison

end
