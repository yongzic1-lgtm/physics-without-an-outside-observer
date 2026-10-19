import Comparison.Elements.TwoThings
import Comparison.Existence.Excursion

/-!
# The grade and the clock in one comparison

The mixed moment on the fifteen two-spinor states other than the singlet, proved as a finite trace.

On the sixteen two-spinor states of two systems (Proposition 10) the **grade** is `N = Σ_u n_u`,
`n_u = (1 − γ_u ⊗ γ_u)/2` (`count`), with `N e = |S| e` on the two-spinor state `e` that disagrees on the lines
`S` (`gradeOp_rel`): `0` on the singlet, `2` on the ten symmetric states, `4` on the five vector states. A source `S`
(a 5 × 5 matrix) acts as **`H_S = −iρ(iS) = −½ Σ_(a,b) S_ab γ_a ⊗ γ_b`** (Proposition 94, as in
RuleAndLaw/Bridges.lean); for a diagonal traceless `S` its value on the two-spinor state disagreeing on `R` is
`Σ_(a∈R) s_a` (`clockOp_diag_rel`). **`τ`** is the normalized trace on the fifteen two-spinor states other than
the singlet (`tau`, `tau_eq_sum_nonnone`).

* `tau_grade`: `τ(N) = 8/3`.
* `tau_clock`, `tau_grade_clock`: `τ(H_S) = 0` and `τ(N H_S) = 0` for a traceless symmetric `S`: the
  currents have zero mean and no covariance with the grade.
* `tau_clock_clock`: `τ(H_S H_T) = (4/15) Tr(ST)`; `tau_grade_clock_clock`: `τ(N H_S H_T) = (2/3) Tr(ST)`.
* `kappa_eq`: **`κ(N, H_S, H_T) = τ[(N − τ(N)) H_S H_T] = −(2/45) Tr(ST)`**; `cumulant`: the connected third
  moment `τ(NH_SH_T) − τ(N)τ(H_SH_T) − τ(H_S)τ(NH_T) − τ(H_T)τ(NH_S) + 2τ(N)τ(H_S)τ(H_T)` is the same.
* `mixed_moment_subspaces`: for `S_D = (5P_D − r)/4` with `Tr P_D = r` and `P_E` symmetric with
  `Tr P_E = s`, **`κ = (rs − 5 Tr(P_DP_E))/72`**; `mixed_moment_complement`: **`r(5 − r)/72`** for a
  symmetric projector and its complement.
* `mixed_moment_lines`: for the own rotations `S_h = (5hhᵀ − 1)/4` of two unit lines,
  **`κ(N, H_h, H_k) = (1 − 5(h·k)²)/72`**; `mixed_moment_orth`: `1/72` for orthogonal lines.
* `subTurn_eq_sum`, `kappa_orth_sets`: the rotation of the span of lines is the sum of their own rotations, and for
  `m` lines orthogonal to `n` lines `κ = mn/72`: the six cross pairs of plane and colour give `6/72`.
* `kappa_one_against_four`: `4/72 = 1/18 = −Φ(1)/(1 + Φ(1))`; `kappa_plane_against_colour`:
  `6/72 = 1/12 = −Φ(i)/(1 + Φ(i))`, with `Φ(1) = −1/19` and `Φ(i) = −1/13` the signed excursion of
  Proposition 30 (`Φ_one`, `Φ_I`); `interior_factor`: `1 + 6/72 = 1 + 6 · (1/72) = 13/12`.
-/

open Matrix hiding J
open Complex Kronecker

namespace Comparison.ArticleStatements

/-! ## 1. The trace on the fifteen two-spinor states other than the singlet -/

/-- **The normalized trace on the fifteen two-spinor states other than the singlet:**
`τ(X) = (Tr X − ⟨Ω, XΩ⟩)/15`. -/
noncomputable def tau (X : Matrix Two Two ℂ) : ℂ := (X.trace - star Ω ⬝ᵥ (X *ᵥ Ω)) / 15

/-- The trace is the sum over the sixteen two-spinor states, an orthonormal basis. -/
theorem trace_eq_sum_rel (X : Matrix Two Two ℂ) :
    X.trace = ∑ k, star (rel k) ⬝ᵥ (X *ᵥ rel k) := by
  let U : Matrix Two (Fin 16) ℂ := Matrix.of fun p k => rel k p
  have hUU : Uᴴ * U = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← rel_inner k l]
    simp only [U, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
  have hUU' : U * Uᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (m := Fin 16) (n := Two) (R := ℂ)
      (by simp [Fintype.card_prod])).mp hUU
  calc X.trace = (X * (U * Uᴴ)).trace := by rw [hUU', Matrix.mul_one]
    _ = (Uᴴ * (X * U)).trace := by rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = ∑ k, star (rel k) ⬝ᵥ (X *ᵥ rel k) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, U, Matrix.conjTranspose_apply,
        Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]

/-- **`τ` is the mean over the fifteen two-spinor states other than the singlet.** -/
theorem tau_eq_sum_nonnone (X : Matrix Two Two ℂ) :
    tau X = (∑ k ∈ Finset.univ.erase 0, star (rel k) ⬝ᵥ (X *ᵥ rel k)) / 15 := by
  rw [tau, trace_eq_sum_rel, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 16)), rel_zero]
  ring

theorem tau_of_singlet (X : Matrix Two Two ℂ) (hX : X *ᵥ Ω = 0) : tau X = X.trace / 15 := by
  rw [tau, hX, dotProduct_zero, sub_zero]

theorem tau_sub (X Y : Matrix Two Two ℂ) : tau (X - Y) = tau X - tau Y := by
  simp only [tau, Matrix.trace_sub, Matrix.sub_mulVec, dotProduct_sub]
  ring

theorem tau_smul (c : ℂ) (X : Matrix Two Two ℂ) : tau (c • X) = c * tau X := by
  simp only [tau, Matrix.trace_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-! ## 2. Traces of the lines -/

theorem trace_γγ (a c : Fin 5) : (γ a * γ c).trace = if a = c then 4 else 0 := by
  by_cases h : a = c
  · subst h
    rw [γ_mul_self, ite_eq_left rfl, Matrix.trace_one]
    simp [Fintype.card_prod]
  · rw [ite_eq_right h]
    have h1 : (γ a * γ c).trace = (γ c * γ a).trace := Matrix.trace_mul_comm _ _
    have h2 : (γ a * γ c).trace = -(γ c * γ a).trace := by rw [γ_anticomm h, Matrix.trace_neg]
    have h3 : (γ c * γ a).trace = 0 := by linear_combination (h2 - h1) / 2
    rw [h1, h3]

theorem exists_other (e a c : Fin 5) : ∃ d : Fin 5, d ≠ e ∧ d ≠ a ∧ d ≠ c := by
  revert e a c
  decide

/-- **Three lines have no trace:** `Tr(γ_e γ_a γ_c) = 0`; a fourth line anticommutes with all three. -/
theorem trace_γγγ (e a c : Fin 5) : (γ e * γ a * γ c).trace = 0 := by
  obtain ⟨d, hde, hda, hdc⟩ := exists_other e a c
  set X := γ e * γ a * γ c with hXdef
  have hX : γ d * X = -(X * γ d) := by
    rw [hXdef]
    calc γ d * (γ e * γ a * γ c) = (γ d * γ e) * γ a * γ c := by noncomm_ring
      _ = -(γ e * (γ d * γ a) * γ c) := by rw [γ_anticomm hde]; noncomm_ring
      _ = γ e * γ a * (γ d * γ c) := by rw [γ_anticomm hda]; noncomm_ring
      _ = -(γ e * γ a * γ c * γ d) := by rw [γ_anticomm hdc]; noncomm_ring
  have ht : X.trace = -X.trace := by
    calc X.trace = (γ d * (γ d * X)).trace := by
          rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
      _ = (γ d * X * γ d).trace := Matrix.trace_mul_comm _ _
      _ = -X.trace := by
        rw [hX, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  linear_combination ht / 2

theorem trace_kron (A B C D : Matrix Four Four ℂ) :
    ((A ⊗ₖ B) * (C ⊗ₖ D)).trace = (A * C).trace * (B * D).trace := by
  rw [← mul_kronecker_mul, trace_kronecker]

theorem trace_kron3 (A B C D E F : Matrix Four Four ℂ) :
    ((A ⊗ₖ B) * (C ⊗ₖ D) * (E ⊗ₖ F)).trace = (A * C * E).trace * (B * D * F).trace := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, trace_kronecker]

/-! ## 3. The grade -/

/-- **The grade** `N = Σ_u n_u`, the number of lines on which a two-spinor state disagrees. -/
noncomputable def gradeOp : Matrix Two Two ℂ := ∑ u, count u

theorem gradeOp_rel (k : Fin 16) :
    gradeOp *ᵥ rel k = ((disagreeSet k).card : ℂ) • rel k := by
  rw [gradeOp, Matrix.sum_mulVec]
  simp only [count_rel]
  rw [← Finset.sum_smul]
  congr 1
  simp

theorem gradeOp_singlet : gradeOp *ᵥ Ω = 0 := by
  rw [← rel_zero, gradeOp_rel]
  simp [disagreeSet]

theorem trace_count (u : Fin 5) : (count u).trace = 8 := by
  rw [count, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, trace_kronecker, γ_trace]
  simp [Fintype.card_prod]
  norm_num

theorem trace_gradeOp : gradeOp.trace = 40 := by
  rw [gradeOp, Matrix.trace_sum]
  simp only [trace_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **`τ(N) = 8/3`.** -/
theorem tau_grade : tau gradeOp = 8 / 3 := by
  rw [tau_of_singlet _ gradeOp_singlet, trace_gradeOp]
  norm_num

/-! ## 4. The clock of a source -/

/-- **The clock generator of a source** `S`: `H_S = −iρ(iS) = −½ Σ_(a,b) S_ab γ_a ⊗ γ_b`. -/
noncomputable def clockOp (S : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Two Two ℂ :=
  ∑ p : Fin 5 × Fin 5, (-(1 / 2) * S p.1 p.2) • (γ p.1 ⊗ₖ γ p.2)

/-- **On the two-spinor states a diagonal traceless source is the sum of its values on the disagreeing lines:**
`H_S e = (Σ_(a∈R) s_a) e` for the two-spinor state `e` disagreeing on `R`. -/
theorem clockOp_diag_rel (s : Fin 5 → ℂ) (hs : ∑ a, s a = 0) (k : Fin 16) :
    clockOp (Matrix.diagonal s) *ᵥ rel k = (∑ a ∈ disagreeSet k, s a) • rel k := by
  have e1 : clockOp (Matrix.diagonal s) = ∑ a, (-(1 / 2) * s a) • (γ a ⊗ₖ γ a) := by
    rw [clockOp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.diagonal_apply_eq]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), mul_zero, zero_smul]
    · simp
  rw [e1, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, agreement, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hD : ∑ a ∈ disagreeSet k, s a =
      ∑ a ∈ Finset.univ.filter (fun a => a ∈ disagreeSet k), s a := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h2 : ∑ a, s a * (if a ∈ disagreeSet k then -1 else 1 : ℂ) =
      ∑ a, s a - 2 * ∑ a ∈ disagreeSet k, s a := by
    simp only [mul_ite, mul_neg, mul_one]
    rw [Finset.sum_ite, hD,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => a ∈ disagreeSet k) s,
      Finset.sum_neg_distrib]
    ring
  have h3 : ∑ a, -(1 / 2) * s a * (if a ∈ disagreeSet k then -1 else 1 : ℂ) =
      -(1 / 2) * ∑ a, s a * (if a ∈ disagreeSet k then -1 else 1 : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h3, h2, hs]
  ring

/-- `Σ_(a,b) T_ab γ_a γ_b = Tr T` for a symmetric `T`. -/
theorem sum_sym_γγ (T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) :
    ∑ a, ∑ b, T a b • (γ a * γ b) = T.trace • (1 : Matrix Four Four ℂ) := by
  have hsym : ∀ a b, T b a = T a b := fun a b => by
    rw [← Matrix.transpose_apply T a b, hT]
  have hswap : ∑ a, ∑ b, T a b • (γ a * γ b) = ∑ a, ∑ b, T a b • (γ b * γ a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym]
  have h2 : ∑ a, ∑ b, T a b • (γ a * γ b) + ∑ a, ∑ b, T a b • (γ b * γ a) =
      ∑ a, ∑ b, (T a b * (if a = b then (2 : ℂ) else 0)) • (1 : Matrix Four Four ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_add, clifford, smul_smul]
  have h3 : ∑ a, ∑ b, (T a b * (if a = b then (2 : ℂ) else 0)) • (1 : Matrix Four Four ℂ) =
      (2 * T.trace) • (1 : Matrix Four Four ℂ) := by
    simp only [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.trace,
      Matrix.diag, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have h4 : (2 : ℂ) • ∑ a, ∑ b, T a b • (γ a * γ b) =
      (2 : ℂ) • (T.trace • (1 : Matrix Four Four ℂ)) := by
    rw [two_smul, smul_smul]
    nth_rewrite 2 [hswap]
    rw [h2, h3]
  exact smul_right_injective _ two_ne_zero h4

/-- `H_T Ω = −½ ((Σ_(a,b) T_ab γ_a γ_b) ⊗ 1) Ω`. -/
theorem clockOp_mulVec_singlet (T : Matrix (Fin 5) (Fin 5) ℂ) :
    clockOp T *ᵥ Ω = (-(1 / 2) : ℂ) • relOf ((∑ a, ∑ b, T a b • (γ a * γ b)) * MΩ) := by
  have h1 : ∀ a b, (γ a ⊗ₖ γ b) *ᵥ Ω = relOf (γ a * γ b * MΩ) := by
    intro a b
    rw [Ω, kron_mulVec_relOf]
    simp only [Matrix.mul_assoc, MΩ_mul_γ_transpose]
  rw [clockOp, Matrix.sum_mulVec, Fintype.sum_prod_type]
  simp only [Matrix.smul_mulVec, h1]
  ext p
  simp only [Finset.sum_apply, Pi.smul_apply, relOf, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **A symmetric traceless source leaves the singlet at rest:** `H_T Ω = 0`. -/
theorem clockOp_singlet (T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    clockOp T *ᵥ Ω = 0 := by
  rw [clockOp_mulVec_singlet, sum_sym_γγ T hT, htr, zero_smul, Matrix.zero_mul]
  ext p
  simp [relOf]

theorem trace_mul_clock (Y : Matrix Two Two ℂ) (S : Matrix (Fin 5) (Fin 5) ℂ) :
    (Y * clockOp S).trace =
      ∑ p : Fin 5 × Fin 5, (-(1 / 2) * S p.1 p.2) * (Y * (γ p.1 ⊗ₖ γ p.2)).trace := by
  rw [clockOp, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem trace_mul_clock_clock (Y : Matrix Two Two ℂ) (S T : Matrix (Fin 5) (Fin 5) ℂ) :
    (Y * clockOp S * clockOp T).trace = ∑ p : Fin 5 × Fin 5, ∑ q : Fin 5 × Fin 5,
      (-(1 / 2) * S p.1 p.2) * (-(1 / 2) * T q.1 q.2) *
        (Y * (γ p.1 ⊗ₖ γ p.2) * (γ q.1 ⊗ₖ γ q.2)).trace := by
  rw [Matrix.mul_assoc, clockOp, clockOp, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

theorem trace_clockOp (S : Matrix (Fin 5) (Fin 5) ℂ) : (clockOp S).trace = 0 := by
  rw [clockOp, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.trace_smul, trace_kronecker, γ_trace, zero_mul, smul_zero]

/-- `Tr(H_S H_T) = 4 Σ_(a,b) S_ab T_ab`. -/
theorem trace_clock_clock (S T : Matrix (Fin 5) (Fin 5) ℂ) :
    (clockOp S * clockOp T).trace = 4 * ∑ p : Fin 5 × Fin 5, S p.1 p.2 * T p.1 p.2 := by
  have h := trace_mul_clock_clock 1 S T
  rw [Matrix.one_mul] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_mul, trace_kron, trace_γγ, trace_γγ, ite_eq_left rfl, ite_eq_left rfl]
    ring
  · intro q _ hq
    rw [Matrix.one_mul, trace_kron, trace_γγ, trace_γγ]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hq (Prod.ext h1 h2).symm
      rw [ite_eq_right h2]
      ring
    · rw [ite_eq_right h1]
      ring
  · intro hp
    exact absurd (Finset.mem_univ p) hp

/-- `Tr((γ_e ⊗ γ_e) H_S H_T) = 0`. -/
theorem trace_γγ_clock_clock (e : Fin 5) (S T : Matrix (Fin 5) (Fin 5) ℂ) :
    ((γ e ⊗ₖ γ e) * clockOp S * clockOp T).trace = 0 := by
  rw [trace_mul_clock_clock]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  rw [trace_kron3, trace_γγγ, zero_mul, mul_zero]

/-- `Tr(N H_S H_T) = 10 Σ_(a,b) S_ab T_ab`. -/
theorem trace_grade_clock_clock (S T : Matrix (Fin 5) (Fin 5) ℂ) :
    (gradeOp * clockOp S * clockOp T).trace = 10 * ∑ p : Fin 5 × Fin 5, S p.1 p.2 * T p.1 p.2 := by
  have h : ∀ u, (count u * clockOp S * clockOp T).trace =
      2 * ∑ p : Fin 5 × Fin 5, S p.1 p.2 * T p.1 p.2 := by
    intro u
    rw [count, Matrix.smul_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.one_mul, trace_clock_clock, trace_γγ_clock_clock, smul_eq_mul]
    ring
  rw [gradeOp, Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `Tr((γ_u ⊗ γ_u) H_S) = −8 S_uu`. -/
theorem trace_γγ_clock (u : Fin 5) (S : Matrix (Fin 5) (Fin 5) ℂ) :
    ((γ u ⊗ₖ γ u) * clockOp S).trace = -8 * S u u := by
  rw [trace_mul_clock, Finset.sum_eq_single (u, u)]
  · dsimp only
    rw [trace_kron, trace_γγ, ite_eq_left rfl]
    ring
  · intro q _ hq
    rw [trace_kron, trace_γγ, trace_γγ]
    by_cases h1 : u = q.1
    · have h2 : u ≠ q.2 := fun h2 => hq (Prod.ext h1.symm h2.symm)
      rw [ite_eq_right h2]
      ring
    · rw [ite_eq_right h1]
      ring
  · intro hp
    exact absurd (Finset.mem_univ _) hp

/-- `Tr(N H_S) = 4 Tr S`. -/
theorem trace_grade_clock (S : Matrix (Fin 5) (Fin 5) ℂ) :
    (gradeOp * clockOp S).trace = 4 * S.trace := by
  have h2 : ∀ u, (count u * clockOp S).trace = 4 * S u u := by
    intro u
    rw [count, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_sub,
      trace_clockOp, trace_γγ_clock, smul_eq_mul]
    ring
  rw [gradeOp, Finset.sum_mul, Matrix.trace_sum, Finset.sum_congr rfl fun u _ => h2 u,
    ← Finset.mul_sum]
  rfl

/-- `Σ_(a,b) S_ab T_ab = Tr(ST)` for a symmetric `T`. -/
theorem sum_pairs_eq_trace (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) :
    ∑ p : Fin 5 × Fin 5, S p.1 p.2 * T p.1 p.2 = (S * T).trace := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Matrix.transpose_apply T a b, hT]

/-! ## 5. The mixed moment -/

/-- **`τ(H_S) = 0`**: a symmetric traceless current has zero mean. -/
theorem tau_clock (S : Matrix (Fin 5) (Fin 5) ℂ) (hS : Sᵀ = S) (htr : S.trace = 0) :
    tau (clockOp S) = 0 := by
  rw [tau_of_singlet _ (clockOp_singlet S hS htr), trace_clockOp, zero_div]

/-- **`τ(N H_S) = 0`**: a symmetric traceless current has no covariance with the grade. -/
theorem tau_grade_clock (S : Matrix (Fin 5) (Fin 5) ℂ) (hS : Sᵀ = S) (htr : S.trace = 0) :
    tau (gradeOp * clockOp S) = 0 := by
  rw [tau_of_singlet _ (by rw [← Matrix.mulVec_mulVec, clockOp_singlet S hS htr, Matrix.mulVec_zero]),
    trace_grade_clock, htr]
  ring

/-- **`τ(H_S H_T) = (4/15) Tr(ST)`.** -/
theorem tau_clock_clock (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    tau (clockOp S * clockOp T) = (4 / 15) * (S * T).trace := by
  rw [tau_of_singlet _ (by rw [← Matrix.mulVec_mulVec, clockOp_singlet T hT htr, Matrix.mulVec_zero]),
    trace_clock_clock, sum_pairs_eq_trace S T hT]
  ring

/-- **`τ(N H_S H_T) = (2/3) Tr(ST)`.** -/
theorem tau_grade_clock_clock (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    tau (gradeOp * clockOp S * clockOp T) = (2 / 3) * (S * T).trace := by
  rw [tau_of_singlet _ (by rw [← Matrix.mulVec_mulVec, clockOp_singlet T hT htr, Matrix.mulVec_zero]),
    trace_grade_clock_clock, sum_pairs_eq_trace S T hT]
  ring

/-- **The connected mixed moment** `κ(N, H_S, H_T) = τ[(N − τ(N)) H_S H_T]`. -/
noncomputable def kappa (S T : Matrix (Fin 5) (Fin 5) ℂ) : ℂ :=
  tau ((gradeOp - tau gradeOp • (1 : Matrix Two Two ℂ)) * clockOp S * clockOp T)

/-- **The mixed moment: `κ(N, H_S, H_T) = τ[(N − 8/3) H_S H_T] = −(2/45) Tr(ST)`** for a
symmetric traceless `T`. -/
theorem kappa_eq (S T : Matrix (Fin 5) (Fin 5) ℂ) (hT : Tᵀ = T) (htr : T.trace = 0) :
    kappa S T = -(2 / 45) * (S * T).trace := by
  have e : (gradeOp - tau gradeOp • (1 : Matrix Two Two ℂ)) * clockOp S * clockOp T =
      gradeOp * clockOp S * clockOp T - tau gradeOp • (clockOp S * clockOp T) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [kappa, e, tau_sub, tau_smul, tau_grade_clock_clock S T hT htr, tau_clock_clock S T hT htr,
    tau_grade]
  ring

/-- **The connected third moment is `κ`:** with zero means the full cumulant
`τ(NH_SH_T) − τ(N)τ(H_SH_T) − τ(H_S)τ(NH_T) − τ(H_T)τ(NH_S) + 2τ(N)τ(H_S)τ(H_T)` is `−(2/45) Tr(ST)`. -/
theorem cumulant (S T : Matrix (Fin 5) (Fin 5) ℂ) (hS : Sᵀ = S) (hSt : S.trace = 0) (hT : Tᵀ = T)
    (hTt : T.trace = 0) :
    tau (gradeOp * clockOp S * clockOp T) - tau gradeOp * tau (clockOp S * clockOp T)
      - tau (clockOp S) * tau (gradeOp * clockOp T) - tau (clockOp T) * tau (gradeOp * clockOp S)
      + 2 * tau gradeOp * tau (clockOp S) * tau (clockOp T) = -(2 / 45) * (S * T).trace := by
  rw [tau_grade_clock_clock S T hT hTt, tau_grade, tau_clock_clock S T hT hTt, tau_clock S hS hSt,
    tau_clock T hT hTt]
  ring

/-! ## 6. Lines and subspaces of the five -/

/-- **The rotation of a subspace** with symmetric `P` and `Tr P = r`: `S = (5P − r)/4`. -/
noncomputable def subTurn (P : Matrix (Fin 5) (Fin 5) ℂ) (r : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 4 : ℂ) • ((5 : ℂ) • P - r • (1 : Matrix (Fin 5) (Fin 5) ℂ))

theorem subTurn_transpose (P : Matrix (Fin 5) (Fin 5) ℂ) (r : ℂ) (hP : Pᵀ = P) :
    (subTurn P r)ᵀ = subTurn P r := by
  rw [subTurn, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_one, hP]

theorem subTurn_trace (P : Matrix (Fin 5) (Fin 5) ℂ) (r : ℂ) (hP : P.trace = r) :
    (subTurn P r).trace = 0 := by
  rw [subTurn, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, hP, Fintype.card_fin]
  simp only [smul_eq_mul]
  push_cast
  ring

theorem subTurn_mul_trace (P Q : Matrix (Fin 5) (Fin 5) ℂ) (r s : ℂ) (hP : P.trace = r)
    (hQ : Q.trace = s) :
    (subTurn P r * subTurn Q s).trace = (25 * (P * Q).trace - 5 * r * s) / 16 := by
  simp only [subTurn, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hP, hQ,
    smul_eq_mul, Fintype.card_fin]
  push_cast
  ring

/-- **The mixed moment of two subspaces:** `κ = (rs − 5 Tr(P_DP_E))/72`. -/
theorem mixed_moment_subspaces (P Q : Matrix (Fin 5) (Fin 5) ℂ) (r s : ℂ) (hQ : Qᵀ = Q)
    (hPr : P.trace = r) (hQs : Q.trace = s) :
    kappa (subTurn P r) (subTurn Q s) = (r * s - 5 * (P * Q).trace) / 72 := by
  rw [kappa_eq _ _ (subTurn_transpose Q s hQ) (subTurn_trace Q s hQs),
    subTurn_mul_trace P Q r s hPr hQs]
  ring

/-- **A subspace against its complement:** `κ = r(5 − r)/72` for a symmetric projector of trace `r`. -/
theorem mixed_moment_complement (P : Matrix (Fin 5) (Fin 5) ℂ) (r : ℂ) (hP : Pᵀ = P)
    (hPP : P * P = P) (hPr : P.trace = r) :
    kappa (subTurn P r) (subTurn (1 - P) (5 - r)) = r * (5 - r) / 72 := by
  have hQ : (1 - P)ᵀ = 1 - P := by rw [Matrix.transpose_sub, Matrix.transpose_one, hP]
  have hQs : (1 - P).trace = 5 - r := by
    rw [Matrix.trace_sub, Matrix.trace_one, hPr, Fintype.card_fin]
    push_cast
    ring
  have hPQ : (P * (1 - P)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, Matrix.trace_zero]
  rw [mixed_moment_subspaces P (1 - P) r (5 - r) hQ hPr hQs, hPQ]
  ring

/-- The projector on a line `h`: `hhᵀ`. -/
noncomputable def lineProj (h : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.vecMulVec (fun a => (h a : ℂ)) (fun a => (h a : ℂ))

/-- **The own rotation of a line** `h`: `S_h = (5hhᵀ − 1)/4`. -/
noncomputable def ownTurn (h : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℂ := subTurn (lineProj h) 1

theorem lineProj_transpose (h : Fin 5 → ℝ) : (lineProj h)ᵀ = lineProj h :=
  Matrix.transpose_vecMulVec _ _

theorem lineProj_trace (h : Fin 5 → ℝ) (hh : ∑ a, h a ^ 2 = 1) : (lineProj h).trace = 1 := by
  simp only [lineProj, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply]
  have e := congrArg (fun x : ℝ => (x : ℂ)) hh
  push_cast at e
  rw [← e]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem lineProj_mul_trace (h k : Fin 5 → ℝ) :
    (lineProj h * lineProj k).trace = ((∑ a, h a * k a : ℝ) : ℂ) ^ 2 := by
  simp only [lineProj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply]
  push_cast
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem ownTurn_transpose (h : Fin 5 → ℝ) : (ownTurn h)ᵀ = ownTurn h :=
  subTurn_transpose _ _ (lineProj_transpose h)

theorem ownTurn_trace (h : Fin 5 → ℝ) (hh : ∑ a, h a ^ 2 = 1) : (ownTurn h).trace = 0 :=
  subTurn_trace _ _ (lineProj_trace h hh)

/-- **Two lines: `κ(N, H_h, H_k) = (1 − 5(h·k)²)/72`.** -/
theorem mixed_moment_lines (h k : Fin 5 → ℝ) (hh : ∑ a, h a ^ 2 = 1) (hk : ∑ a, k a ^ 2 = 1) :
    kappa (ownTurn h) (ownTurn k) = (1 - 5 * ((∑ a, h a * k a : ℝ) : ℂ) ^ 2) / 72 := by
  rw [ownTurn, ownTurn, mixed_moment_subspaces _ _ 1 1 (lineProj_transpose k) (lineProj_trace h hh)
    (lineProj_trace k hk), lineProj_mul_trace]
  ring

/-- **Two orthogonal lines: `κ = 1/72`.** -/
theorem mixed_moment_orth (h k : Fin 5 → ℝ) (hh : ∑ a, h a ^ 2 = 1) (hk : ∑ a, k a ^ 2 = 1)
    (hhk : ∑ a, h a * k a = 0) : kappa (ownTurn h) (ownTurn k) = 1 / 72 := by
  rw [mixed_moment_lines h k hh hk, hhk]
  norm_num

/-- **The rotation of the span of lines is the sum of their own rotations:**
`(5 Σ_i v_iv_iᵀ − m)/4 = Σ_i (5v_iv_iᵀ − 1)/4`. -/
theorem subTurn_eq_sum {m : ℕ} (v : Fin m → Fin 5 → ℝ) :
    subTurn (∑ i, lineProj (v i)) m = ∑ i, ownTurn (v i) := by
  simp only [ownTurn, subTurn, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, one_smul]
  congr 1
  rw [Finset.smul_sum]
  congr 1
  exact Nat.cast_smul_eq_nsmul ℂ m 1

/-- `κ` is additive in each source. -/
theorem kappa_sum {m n : ℕ} (S : Fin m → Matrix (Fin 5) (Fin 5) ℂ) (T : Fin n → Matrix (Fin 5) (Fin 5) ℂ)
    (hT : ∀ j, (T j)ᵀ = T j) (htr : ∀ j, (T j).trace = 0) :
    kappa (∑ i, S i) (∑ j, T j) = ∑ i, ∑ j, kappa (S i) (T j) := by
  have hTs : (∑ j, T j)ᵀ = ∑ j, T j := by
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun j _ => hT j
  have htrs : (∑ j, T j).trace = 0 := by
    rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero fun j _ => htr j
  rw [kappa_eq _ _ hTs htrs, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kappa_eq _ _ (hT j) (htr j)]

/-- **`m` lines against `n` lines orthogonal to them: `κ = mn/72`**, one `1/72` for each cross pair. -/
theorem kappa_orth_sets {m n : ℕ} (v : Fin m → Fin 5 → ℝ) (w : Fin n → Fin 5 → ℝ)
    (hv : ∀ i, ∑ a, v i a ^ 2 = 1) (hw : ∀ j, ∑ a, w j a ^ 2 = 1)
    (hvw : ∀ i j, ∑ a, v i a * w j a = 0) :
    kappa (subTurn (∑ i, lineProj (v i)) m) (subTurn (∑ j, lineProj (w j)) n) = (m * n : ℂ) / 72 := by
  rw [subTurn_eq_sum, subTurn_eq_sum,
    kappa_sum _ _ (fun j => ownTurn_transpose (w j)) (fun j => ownTurn_trace (w j) (hw j))]
  simp only [fun i j => mixed_moment_orth (v i) (w j) (hv i) (hw j) (hvw i j), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **One line against its other four: `κ = 4/72 = 1/18 = −Φ(1)/(1 + Φ(1))`**, `Φ(1) = −1/19`. -/
theorem kappa_one_against_four (P : Matrix (Fin 5) (Fin 5) ℂ) (hP : Pᵀ = P) (hPP : P * P = P)
    (hPr : P.trace = 1) :
    kappa (subTurn P 1) (subTurn (1 - P) (5 - 1)) = 1 / 18 ∧
      (1 / 18 : ℝ) = -(∑' n, signedLaw n) / (1 + ∑' n, signedLaw n) := by
  refine ⟨?_, ?_⟩
  · rw [mixed_moment_complement P 1 hP hPP hPr]
    norm_num
  · rw [Φ_one.tsum_eq]
    norm_num

/-- **The plane against its colour: `κ = 6/72 = 1/12 = −Φ(i)/(1 + Φ(i))`**, `Φ(i) = −1/13`. -/
theorem kappa_plane_against_colour (P : Matrix (Fin 5) (Fin 5) ℂ) (hP : Pᵀ = P) (hPP : P * P = P)
    (hPr : P.trace = 2) :
    kappa (subTurn P 2) (subTurn (1 - P) (5 - 2)) = 1 / 12 ∧
      (1 / 12 : ℂ) = -(∑' n, (signedLaw n : ℂ) * I ^ n) / (1 + ∑' n, (signedLaw n : ℂ) * I ^ n) := by
  refine ⟨?_, ?_⟩
  · rw [mixed_moment_complement P 2 hP hPP hPr]
    norm_num
  · rw [Φ_I.tsum_eq]
    norm_num

/-- **The interior factor:** `1 + κ(F, C) = 1 + 6 · (1/72) = 13/12`. -/
theorem interior_factor : (1 : ℂ) + 2 * 3 / 72 = 13 / 12 ∧ (1 : ℂ) + 6 * (1 / 72) = 13 / 12 := by
  norm_num

end Comparison.ArticleStatements

#print axioms Comparison.ArticleStatements.trace_eq_sum_rel
#print axioms Comparison.ArticleStatements.tau_eq_sum_nonnone
#print axioms Comparison.ArticleStatements.tau_of_singlet
#print axioms Comparison.ArticleStatements.tau_sub
#print axioms Comparison.ArticleStatements.tau_smul
#print axioms Comparison.ArticleStatements.trace_γγ
#print axioms Comparison.ArticleStatements.exists_other
#print axioms Comparison.ArticleStatements.trace_γγγ
#print axioms Comparison.ArticleStatements.trace_kron
#print axioms Comparison.ArticleStatements.trace_kron3
#print axioms Comparison.ArticleStatements.gradeOp_rel
#print axioms Comparison.ArticleStatements.gradeOp_singlet
#print axioms Comparison.ArticleStatements.trace_count
#print axioms Comparison.ArticleStatements.trace_gradeOp
#print axioms Comparison.ArticleStatements.tau_grade
#print axioms Comparison.ArticleStatements.clockOp_diag_rel
#print axioms Comparison.ArticleStatements.sum_sym_γγ
#print axioms Comparison.ArticleStatements.clockOp_mulVec_singlet
#print axioms Comparison.ArticleStatements.clockOp_singlet
#print axioms Comparison.ArticleStatements.trace_mul_clock
#print axioms Comparison.ArticleStatements.trace_mul_clock_clock
#print axioms Comparison.ArticleStatements.trace_clockOp
#print axioms Comparison.ArticleStatements.trace_clock_clock
#print axioms Comparison.ArticleStatements.trace_γγ_clock_clock
#print axioms Comparison.ArticleStatements.trace_grade_clock_clock
#print axioms Comparison.ArticleStatements.trace_γγ_clock
#print axioms Comparison.ArticleStatements.trace_grade_clock
#print axioms Comparison.ArticleStatements.sum_pairs_eq_trace
#print axioms Comparison.ArticleStatements.tau_clock
#print axioms Comparison.ArticleStatements.tau_grade_clock
#print axioms Comparison.ArticleStatements.tau_clock_clock
#print axioms Comparison.ArticleStatements.tau_grade_clock_clock
#print axioms Comparison.ArticleStatements.kappa_eq
#print axioms Comparison.ArticleStatements.cumulant
#print axioms Comparison.ArticleStatements.subTurn_transpose
#print axioms Comparison.ArticleStatements.subTurn_trace
#print axioms Comparison.ArticleStatements.subTurn_mul_trace
#print axioms Comparison.ArticleStatements.mixed_moment_subspaces
#print axioms Comparison.ArticleStatements.mixed_moment_complement
#print axioms Comparison.ArticleStatements.lineProj_transpose
#print axioms Comparison.ArticleStatements.lineProj_trace
#print axioms Comparison.ArticleStatements.lineProj_mul_trace
#print axioms Comparison.ArticleStatements.ownTurn_transpose
#print axioms Comparison.ArticleStatements.ownTurn_trace
#print axioms Comparison.ArticleStatements.mixed_moment_lines
#print axioms Comparison.ArticleStatements.mixed_moment_orth
#print axioms Comparison.ArticleStatements.subTurn_eq_sum
#print axioms Comparison.ArticleStatements.kappa_sum
#print axioms Comparison.ArticleStatements.kappa_orth_sets
#print axioms Comparison.ArticleStatements.kappa_one_against_four
#print axioms Comparison.ArticleStatements.kappa_plane_against_colour
#print axioms Comparison.ArticleStatements.interior_factor
