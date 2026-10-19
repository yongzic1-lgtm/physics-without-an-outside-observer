import Comparison.Elements.Overlap
import Comparison.Elements.OneThing

/-!
# A massive line on the null cone of the six, and the chiral rotation of the mass
(Propositions 164 and 165)

* `eigen_null_cone` (**Proposition 164**): for real `t`, **`ω` is an eigenvalue of `H = Σ_s t_s γ_s` exactly when
  `ω² = Σ_s t_s²`**, i.e. when `(ω; t)` is null on P3's real six; `step_energy`: a line that holds `h` and moves
  along `j` has `H = μγ_h + kγ_j`, `H² = (μ² + k²) 1`, and its energies are `ω² = μ² + k²`: `E² = p² + m²`.
* `chiral_rotation` (**Proposition 165**): on the plane `F = {h, k}` (`h = 0`, `k = 1`, the colour lines `2, 3, 4`),
  `R(θ) = cos(θ/2) + sin(θ/2) γ_hγ_k = e^{θγ_hγ_k/2}` has `R(θ)R(−θ) = 1` and takes the mass
  `H = Σ_c p_c γ_c + mγ_h + m₅γ_k` to `Σ_c p_c γ_c + (m cos θ + m₅ sin θ)γ_h + (m₅ cos θ − m sin θ)γ_k`: **it keeps `p`
  and the rest mass `m₀ = (m² + m₅²)^{1/2}`**, and `H² = (|p|² + m² + m₅²) 1`.
-/

namespace Comparison.Article

open Matrix hiding J
open Complex

/-! ## Proposition 164: the null cone -/

theorem trace_γv (n : Fin 5 → ℝ) : (γv n).trace = 0 := by
  simp [γv, Matrix.trace_sum, Matrix.trace_smul, γ_trace]

/-- **Proposition 164: `ω` is an eigenvalue of `Σ_s t_s γ_s` exactly when `ω² = |t|²`.** -/
theorem eigen_null_cone (n : Fin 5 → ℝ) (ω : ℝ) :
    (∃ v : Four → ℂ, v ≠ 0 ∧ γv n *ᵥ v = (ω : ℂ) • v) ↔ ω ^ 2 = ∑ s, n s ^ 2 := by
  have hsq := γv_mul_self n
  constructor
  · rintro ⟨v, hv, hH⟩
    have h2 : (γv n * γv n) *ᵥ v = ((ω : ℂ) ^ 2) • v := by
      rw [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, hH, smul_smul, sq]
    rw [hsq, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
    have h3 : (((∑ s, n s ^ 2 : ℝ)) : ℂ) = (ω : ℂ) ^ 2 := smul_left_injective ℂ hv h2
    have h4 : ((∑ s, n s ^ 2 : ℝ) : ℂ) = ((ω ^ 2 : ℝ) : ℂ) := by rw [h3]; push_cast; ring
    exact (Complex.ofReal_injective h4).symm
  · intro hω
    set M := γv n - (ω : ℂ) • (1 : Matrix Four Four ℂ) with hM
    have hprod : M * (γv n + (ω : ℂ) • (1 : Matrix Four Four ℂ)) = 0 := by
      rw [hM, sub_mul, mul_add, mul_add, hsq, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← hω]
      push_cast
      rw [sq]
      abel
    have hdet : M.det = 0 := by
      by_contra hne
      have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hne)
      have hX : γv n + (ω : ℂ) • (1 : Matrix Four Four ℂ) = 0 := (hunit.mul_right_eq_zero).mp hprod
      have htr := congrArg Matrix.trace hX
      rw [Matrix.trace_add, trace_γv, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_zero] at htr
      simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul, zero_add] at htr
      have hω0 : (ω : ℂ) = 0 := by
        have : (ω : ℂ) * 4 = 0 := by simpa using htr
        simpa using this
      have hω0' : ω = 0 := by exact_mod_cast hω0
      have hn : ∀ s, n s = 0 := by
        have h0 : ∑ s, n s ^ 2 = 0 := by rw [← hω, hω0']; ring
        intro s
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => sq_nonneg (n s))).mp h0 s
          (Finset.mem_univ s)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hγ : γv n = 0 := by simp [γv, hn]
      apply hne
      rw [hM, hγ, hω0]
      simp
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hv, ?_⟩
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
    exact hMv

/-- **A step that holds `h` and moves along `j`:** `H = μγ_h + kγ_j` has `H² = (μ² + k²) 1`, and `ω` is one of
its energies exactly when `ω² = μ² + k²`. -/
theorem step_energy {h j : Fin 5} (hj : h ≠ j) (μ k ω : ℝ) :
    ((μ : ℂ) • γ h + (k : ℂ) • γ j) * ((μ : ℂ) • γ h + (k : ℂ) • γ j) =
        ((μ ^ 2 + k ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) ∧
      ((∃ v : Four → ℂ, v ≠ 0 ∧ ((μ : ℂ) • γ h + (k : ℂ) • γ j) *ᵥ v = (ω : ℂ) • v) ↔
        ω ^ 2 = μ ^ 2 + k ^ 2) := by
  let n : Fin 5 → ℝ := fun s => (if s = h then μ else 0) + (if s = j then k else 0)
  have hn : γv n = (μ : ℂ) • γ h + (k : ℂ) • γ j := by
    simp only [γv, n, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single h (fun b _ hb => by simp [hb]) (by simp)]
      simp
    · rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp
  have hn2 : ∑ s, n s ^ 2 = μ ^ 2 + k ^ 2 := by
    simp only [n, add_sq, Finset.sum_add_distrib]
    have e1 : ∑ s : Fin 5, (if s = h then μ else 0) ^ 2 = μ ^ 2 := by
      simp only [ite_pow, zero_pow two_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have e2 : ∑ s : Fin 5, (if s = j then k else 0) ^ 2 = k ^ 2 := by
      simp only [ite_pow, zero_pow two_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have e3 : ∑ s : Fin 5, 2 * (if s = h then μ else 0) * (if s = j then k else 0) = 0 := by
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases h1 : s = h
      · subst h1; simp [hj]
      · simp [h1]
    rw [e1, e2, e3]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hn, γv_mul_self, hn2]
  · rw [← hn, eigen_null_cone, hn2]

/-! ## Proposition 165: the chiral rotation of the mass -/

/-- `R(θ) = cos(θ/2) + sin(θ/2) γ_hγ_k`, the plane's rotation by `θ` (`h = 0`, `k = 1`). -/
noncomputable def chiralR (θ : ℝ) : Matrix Four Four ℂ :=
  ((Real.cos (θ / 2) : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) + ((Real.sin (θ / 2) : ℝ) : ℂ) • (γ 0 * γ 1)

theorem planeX_sq : (γ 0 * γ 1) * (γ 0 * γ 1) = -1 := by
  rw [show γ 0 * γ 1 * (γ 0 * γ 1) = γ 0 * (γ 1 * γ 0) * γ 1 by simp only [Matrix.mul_assoc],
    γ_anticomm (show (1 : Fin 5) ≠ 0 by decide), Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc,
    γ_mul_self, Matrix.one_mul, γ_mul_self]

theorem rot_conj_anti {X g : Matrix Four Four ℂ} (hXX : X * X = -1) (hg : g * X = -(X * g)) (c s : ℂ) :
    (c • (1 : Matrix Four Four ℂ) + s • X) * g * (c • 1 - s • X) =
      (c ^ 2 - s ^ 2) • g + (2 * c * s) • (X * g) := by
  have h3 : X * g * X = g := by
    rw [Matrix.mul_assoc, hg, Matrix.mul_neg, ← Matrix.mul_assoc, hXX]
    simp
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hg, h3]
  module

theorem rot_conj_comm {X g : Matrix Four Four ℂ} (hXX : X * X = -1) (hg : g * X = X * g) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (c • (1 : Matrix Four Four ℂ) + s • X) * g * (c • 1 - s • X) = g := by
  have h3 : X * g * X = -g := by
    rw [Matrix.mul_assoc, hg, ← Matrix.mul_assoc, hXX]
    simp
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hg, h3]
  have : g = (c ^ 2 + s ^ 2) • g := by rw [hcs, one_smul]
  conv_rhs => rw [this]
  module

theorem chiralR_neg (θ : ℝ) :
    chiralR (-θ) = ((Real.cos (θ / 2) : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) -
      ((Real.sin (θ / 2) : ℝ) : ℂ) • (γ 0 * γ 1) := by
  rw [chiralR, neg_div, Real.cos_neg, Real.sin_neg]
  push_cast
  rw [neg_smul, sub_eq_add_neg]

theorem half_angle (θ : ℝ) :
    ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 - ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 = ((Real.cos θ : ℝ) : ℂ) ∧
      2 * ((Real.cos (θ / 2) : ℝ) : ℂ) * ((Real.sin (θ / 2) : ℝ) : ℂ) = ((Real.sin θ : ℝ) : ℂ) ∧
      ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 + ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 = 1 := by
  have e : θ = 2 * (θ / 2) := by ring
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    conv_lhs => rw [e]
    rw [Real.cos_two_mul]
    linarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    conv_lhs => rw [e]
    rw [Real.sin_two_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; push_cast; ring
  · rw [hs]; push_cast; ring
  · have h1 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := by linarith
    exact_mod_cast h1

/-- `R(θ)R(−θ) = 1`. -/
theorem chiralR_inv (θ : ℝ) : chiralR θ * chiralR (-θ) = 1 := by
  rw [chiralR, chiralR_neg]
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    planeX_sq]
  have h := (half_angle θ).2.2
  conv_rhs => rw [← one_smul ℂ (1 : Matrix Four Four ℂ), ← h]
  module

theorem chiral_γ0 (θ : ℝ) :
    chiralR θ * γ 0 * chiralR (-θ) = ((Real.cos θ : ℝ) : ℂ) • γ 0 - ((Real.sin θ : ℝ) : ℂ) • γ 1 := by
  have hX0 : (γ 0 * γ 1) * γ 0 = -γ 1 := by
    rw [Matrix.mul_assoc, γ_anticomm (show (1 : Fin 5) ≠ 0 by decide), Matrix.mul_neg, ← Matrix.mul_assoc,
      γ_mul_self, Matrix.one_mul]
  have hg : γ 0 * (γ 0 * γ 1) = -((γ 0 * γ 1) * γ 0) := by
    rw [hX0, neg_neg, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  rw [chiralR, chiralR_neg, rot_conj_anti planeX_sq hg, (half_angle θ).1, (half_angle θ).2.1, hX0]
  rw [smul_neg, sub_eq_add_neg]

theorem chiral_γ1 (θ : ℝ) :
    chiralR θ * γ 1 * chiralR (-θ) = ((Real.cos θ : ℝ) : ℂ) • γ 1 + ((Real.sin θ : ℝ) : ℂ) • γ 0 := by
  have hX1 : (γ 0 * γ 1) * γ 1 = γ 0 := by
    rw [Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  have hg : γ 1 * (γ 0 * γ 1) = -((γ 0 * γ 1) * γ 1) := by
    rw [hX1, ← Matrix.mul_assoc, γ_anticomm (show (1 : Fin 5) ≠ 0 by decide), Matrix.neg_mul,
      Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  rw [chiralR, chiralR_neg, rot_conj_anti planeX_sq hg, (half_angle θ).1, (half_angle θ).2.1, hX1]

theorem chiral_γc (θ : ℝ) {c : Fin 5} (h0 : c ≠ 0) (h1 : c ≠ 1) :
    chiralR θ * γ c * chiralR (-θ) = γ c := by
  have hg : γ c * (γ 0 * γ 1) = (γ 0 * γ 1) * γ c := by
    rw [← Matrix.mul_assoc, γ_anticomm h0, Matrix.neg_mul, Matrix.mul_assoc, γ_anticomm h1, Matrix.mul_neg,
      neg_neg, Matrix.mul_assoc]
  rw [chiralR, chiralR_neg, rot_conj_comm planeX_sq hg _ _ (half_angle θ).2.2]

/-- **Proposition 165: the chiral rotation keeps `p` and the rest mass.** -/
theorem chiral_rotation (θ m m₅ p₂ p₃ p₄ : ℝ) :
    chiralR θ * ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) *
        chiralR (-θ) =
      (p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 +
        ((m * Real.cos θ + m₅ * Real.sin θ : ℝ) : ℂ) • γ 0 +
        ((m₅ * Real.cos θ - m * Real.sin θ : ℝ) : ℂ) • γ 1 ∧
      (m * Real.cos θ + m₅ * Real.sin θ) ^ 2 + (m₅ * Real.cos θ - m * Real.sin θ) ^ 2 = m ^ 2 + m₅ ^ 2 ∧
      ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) *
        ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) =
        ((p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2 + m ^ 2 + m₅ ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [chiral_γc θ (by decide) (by decide), chiral_γc θ (by decide) (by decide),
      chiral_γc θ (by decide) (by decide), chiral_γ0, chiral_γ1]
    push_cast
    module
  · have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  · have h := γv_mul_self ![m, m₅, p₂, p₃, p₄]
    have hv : γv ![m, m₅, p₂, p₃, p₄] =
        (p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1 := by
      simp only [γv, Fin.sum_univ_five]
      simp
      abel
    rw [← hv, h]
    congr 2
    simp only [Fin.sum_univ_five]
    simp
    ring

end Comparison.Article
