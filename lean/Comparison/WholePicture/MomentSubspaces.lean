import Comparison.ArticleStatements.MixedMoment

/-!
# The whole picture, statement 12: the mixed moment for every central weight and every two subspaces

`Moment.lean` proves
`𝒥_DE = 𝒞_W (rs − 5 Tr P_DP_E)/72` for every central weight when `D` and `E` are sets of lines; `ArticleStatements/MixedMoment.lean` proves it for every two subspaces at the uniform weight
(`mixed_moment_subspaces`). Here both at once, on the operators of the sixteen two-spinor states:
`H_S = −½ Σ_(a,b) S_ab γ_a ⊗ γ_b` (`clockOp`), the grade `N` (`gradeOp`), the two-spinor states `e_k`
(`rel`, `relGrade k = |k|`: `0` on the singlet, `2` on the ten symmetric states, `4` on the five vector states).
A central weight is a function of the grade, `w₂` on the symmetric states and `w₄` on the vector states
(`centralW`), and with `μ_W = Σ W|k|/Σ W`

  `𝒥_W(S, T) = Σ_k W_k (|k| − μ_W) ⟨e_k, H_SH_T e_k⟩ / Σ_k W_k`,   `𝒞_W = (9/8) Var_W |k|`.

* `plane_line_sums`: for a symmetric traceless `T`, **`Σ_planes ⟨e_k, H_SH_Te_k⟩ = 3 Tr(ST)` and
  `Σ_lines ⟨e_k, H_SH_Te_k⟩ = Tr(ST)`**, from `Tr(H_SH_T) = 4 Tr(ST)`, `Tr(NH_SH_T) = 10 Tr(ST)` and
  the singlet at rest (`trace_clock_clock`, `trace_grade_clock_clock`, `clockOp_singlet`).
* `wClock_eq`: `𝒞_W = 225 w₂w₄/(10w₂ + 5w₄)²`; `wMoment_eq`:
  `𝒥_W(S, T) = −10 w₂w₄ Tr(ST)/(10w₂ + 5w₄)²`.
* `mixed_moment_central_subspaces`: **`𝒥_W(S_D, S_E) = 𝒞_W (rs − 5 Tr P_DP_E)/72` for every central
  weight and every two subspaces** (`S_D = (5P_D − r)/4`, `Tr P_D = r`, `P_E` symmetric,
  `Tr P_E = s`).
* `wMoment_uniform`: at the uniform weight `𝒥_W` is `κ(N, H_S, H_T)`.
-/

open Matrix hiding J
open Complex Kronecker

namespace Comparison.WholePicture

open Comparison.ArticleStatements

/-- The grade of the sixteen two-spinor states: `0` on the singlet, `4` on the five vector states, `2` on the ten
symmetric states. -/
def relGrade : Fin 16 → ℕ := ![0, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

theorem card_disagreeSet : ∀ k : Fin 16, (disagreeSet k).card = relGrade k := by
  decide

/-- **A central weight:** a function of the grade, `w₂` on the ten symmetric states, `w₄` on the five vector
states, nothing on the singlet. -/
def centralW (w₂ w₄ : ℂ) (k : Fin 16) : ℂ :=
  if relGrade k = 2 then w₂ else if relGrade k = 4 then w₄ else 0

/-- The ten symmetric states and the five vector states. -/
def planeRels : Finset (Fin 16) := Finset.univ.filter fun k => relGrade k = 2

def lineRels : Finset (Fin 16) := Finset.univ.filter fun k => relGrade k = 4

/-- The diagonal entry `⟨e_k, Y e_k⟩` of an operator on the two-spinor state `k`. -/
noncomputable def relEntry (Y : Matrix Two Two ℂ) (k : Fin 16) : ℂ := star (rel k) ⬝ᵥ (Y *ᵥ rel k)

theorem sum_relEntry (Y : Matrix Two Two ℂ) : ∑ k, relEntry Y k = Y.trace :=
  (trace_eq_sum_rel Y).symm

theorem sum_grade_relEntry (Y : Matrix Two Two ℂ) :
    ∑ k, (relGrade k : ℂ) * relEntry Y k = (gradeOp * Y).trace := by
  rw [Matrix.trace_mul_comm, trace_eq_sum_rel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [relEntry, ← Matrix.mulVec_mulVec, gradeOp_rel, Matrix.mulVec_smul, dotProduct_smul,
    card_disagreeSet, smul_eq_mul]

/-- **The singlet stays at rest:** `⟨Ω, H_SH_TΩ⟩ = 0` for a symmetric traceless `T`. -/
theorem relEntry_singlet_clock (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    relEntry (clockOp S * clockOp T) 0 = 0 := by
  rw [relEntry, rel_zero, ← Matrix.mulVec_mulVec, clockOp_singlet T hT htr, Matrix.mulVec_zero,
    dotProduct_zero]

/-- The sum over the sixteen splits into the singlet, the symmetric states and the vector states. -/
theorem grade_split (g : Fin 16 → ℂ) :
    ∑ k, g k = g 0 + ∑ k ∈ planeRels, g k + ∑ k ∈ lineRels, g k ∧
      ∑ k, (relGrade k : ℂ) * g k = 2 * ∑ k ∈ planeRels, g k + 4 * ∑ k ∈ lineRels, g k := by
  rw [planeRels, lineRels, Finset.sum_filter, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, relGrade, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  constructor <;> norm_num <;> ring

/-- **The grade-resolved sums:** `Σ_planes ⟨e_k, H_SH_Te_k⟩ = 3 Tr(ST)`, `Σ_lines ⟨e_k, H_SH_Te_k⟩ =
Tr(ST)` for a symmetric traceless `T`. -/
theorem plane_line_sums (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    ∑ k ∈ planeRels, relEntry (clockOp S * clockOp T) k = 3 * (S * T).trace ∧
      ∑ k ∈ lineRels, relEntry (clockOp S * clockOp T) k = (S * T).trace := by
  obtain ⟨e1, e2⟩ := grade_split (relEntry (clockOp S * clockOp T))
  have h1 : ∑ k, relEntry (clockOp S * clockOp T) k = 4 * (S * T).trace := by
    rw [sum_relEntry, trace_clock_clock, sum_pairs_eq_trace S T hT]
  have h2 : ∑ k, (relGrade k : ℂ) * relEntry (clockOp S * clockOp T) k = 10 * (S * T).trace := by
    rw [sum_grade_relEntry, ← Matrix.mul_assoc, trace_grade_clock_clock, sum_pairs_eq_trace S T hT]
  have g0 := relEntry_singlet_clock S T hT htr
  rw [g0, zero_add] at e1
  constructor
  · linear_combination 2 * h1 - h2 / 2 - 2 * e1 + e2 / 2
  · linear_combination h2 / 2 - h1 + e1 - e2 / 2

/-- The total of a central weight, `Σ_k W_k`. -/
def wZ (w₂ w₄ : ℂ) : ℂ := ∑ k, centralW w₂ w₄ k

/-- The mean grade `μ_W = Σ W|k|/Σ W`. -/
noncomputable def wMean (w₂ w₄ : ℂ) : ℂ := (∑ k, centralW w₂ w₄ k * (relGrade k : ℂ)) / wZ w₂ w₄

/-- The variance of the grade, `Var_W |k|`. -/
noncomputable def wVar (w₂ w₄ : ℂ) : ℂ :=
  (∑ k, centralW w₂ w₄ k * (relGrade k : ℂ) ^ 2) / wZ w₂ w₄ - wMean w₂ w₄ ^ 2

/-- **The clock of a central weight,** `𝒞_W = (9/8) Var_W |k|`. -/
noncomputable def wClock (w₂ w₄ : ℂ) : ℂ := 9 / 8 * wVar w₂ w₄

/-- **The mixed moment at a central weight:**
`𝒥_W(S, T) = Σ_k W_k (|k| − μ_W) ⟨e_k, H_SH_Te_k⟩/Σ W`. -/
noncomputable def wMoment (w₂ w₄ : ℂ) (S T : Matrix (Fin 5) (Fin 5) ℂ) : ℂ :=
  (∑ k, centralW w₂ w₄ k * ((relGrade k : ℂ) - wMean w₂ w₄) * relEntry (clockOp S * clockOp T) k) /
    wZ w₂ w₄

theorem central_sums (w₂ w₄ : ℂ) :
    wZ w₂ w₄ = 10 * w₂ + 5 * w₄ ∧
      ∑ k, centralW w₂ w₄ k * (relGrade k : ℂ) = 20 * w₂ + 20 * w₄ ∧
      ∑ k, centralW w₂ w₄ k * (relGrade k : ℂ) ^ 2 = 40 * w₂ + 80 * w₄ := by
  simp only [wZ, centralW, Fin.sum_univ_succ, Fin.sum_univ_zero, relGrade, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> ring

theorem wMean_eq (w₂ w₄ : ℂ) : wMean w₂ w₄ = (20 * w₂ + 20 * w₄) / (10 * w₂ + 5 * w₄) := by
  rw [wMean, (central_sums w₂ w₄).2.1, (central_sums w₂ w₄).1]

/-- **`𝒞_W = 225 w₂w₄/(10w₂ + 5w₄)²`.** -/
theorem wClock_eq (w₂ w₄ : ℂ) :
    wClock w₂ w₄ = 225 * w₂ * w₄ / (10 * w₂ + 5 * w₄) ^ 2 := by
  rw [wClock, wVar, wMean_eq, (central_sums w₂ w₄).2.2, (central_sums w₂ w₄).1]
  field_simp
  ring

/-- Any function of the grade on a sum that vanishes at the singlet is read by the two grade-resolved
sums. -/
theorem central_moment_sum (g : Fin 16 → ℂ) (g0 : g 0 = 0) (X : ℂ) (h1 : ∑ k, g k = 4 * X)
    (h2 : ∑ k, (relGrade k : ℂ) * g k = 10 * X) (w₂ w₄ μ : ℂ) :
    ∑ k, centralW w₂ w₄ k * ((relGrade k : ℂ) - μ) * g k =
      X * (3 * w₂ * (2 - μ) + w₄ * (4 - μ)) := by
  simp only [centralW, Fin.sum_univ_succ, Fin.sum_univ_zero, relGrade, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at h1 h2 ⊢
  norm_num at h1 h2 ⊢
  linear_combination (w₄ * (4 - μ) / 2 - w₂ * (2 - μ) / 2) * h2 +
    (2 * w₂ * (2 - μ) - w₄ * (4 - μ)) * h1 + (w₄ * (4 - μ) - 2 * w₂ * (2 - μ)) * g0

/-- **`𝒥_W(S, T) = −10 w₂w₄ Tr(ST)/(10w₂ + 5w₄)²`** for a symmetric traceless `T`. -/
theorem wMoment_eq (w₂ w₄ : ℂ) (hZ : 10 * w₂ + 5 * w₄ ≠ 0) (S T : Matrix (Fin 5) (Fin 5) ℂ)
    (hT : Tᵀ = T) (htr : T.trace = 0) :
    wMoment w₂ w₄ S T = -10 * w₂ * w₄ * (S * T).trace / (10 * w₂ + 5 * w₄) ^ 2 := by
  have g0 := relEntry_singlet_clock S T hT htr
  have h1 : ∑ k, relEntry (clockOp S * clockOp T) k = 4 * (S * T).trace := by
    rw [sum_relEntry, trace_clock_clock, sum_pairs_eq_trace S T hT]
  have h2 : ∑ k, (relGrade k : ℂ) * relEntry (clockOp S * clockOp T) k = 10 * (S * T).trace := by
    rw [sum_grade_relEntry, ← Matrix.mul_assoc, trace_grade_clock_clock, sum_pairs_eq_trace S T hT]
  rw [wMoment, central_moment_sum _ g0 _ h1 h2, (central_sums w₂ w₄).1, wMean_eq]
  set Z := 10 * w₂ + 5 * w₄ with hZdef
  clear_value Z
  have hZi : Z * Z⁻¹ = 1 := mul_inv_cancel₀ hZ
  linear_combination (-(S * T).trace * Z⁻¹ * (6 * w₂ + 4 * w₄)) * hZi +
    ((S * T).trace * Z⁻¹ ^ 2 * (6 * w₂ + 4 * w₄)) * hZdef

/-- **The mixed moment for every central weight and every two subspaces:**
`𝒥_W(S_D, S_E) = 𝒞_W (rs − 5 Tr P_DP_E)/72`. -/
theorem mixed_moment_central_subspaces (P Q : Matrix (Fin 5) (Fin 5) ℂ) (r s : ℂ) (hQ : Qᵀ = Q)
    (hPr : P.trace = r) (hQs : Q.trace = s) (w₂ w₄ : ℂ) (hZ : 10 * w₂ + 5 * w₄ ≠ 0) :
    wMoment w₂ w₄ (subTurn P r) (subTurn Q s) =
      wClock w₂ w₄ * (r * s - 5 * (P * Q).trace) / 72 := by
  rw [wMoment_eq w₂ w₄ hZ _ _ (subTurn_transpose Q s hQ) (subTurn_trace Q s hQs),
    subTurn_mul_trace P Q r s hPr hQs, wClock_eq w₂ w₄]
  field_simp
  ring

/-- **At the uniform weight the mixed moment is `κ(N, H_S, H_T)`.** -/
theorem wMoment_uniform (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    wMoment 1 1 S T = kappa S T := by
  rw [wMoment_eq 1 1 (by norm_num) S T hT htr, kappa_eq S T hT htr]
  ring

end Comparison.WholePicture
