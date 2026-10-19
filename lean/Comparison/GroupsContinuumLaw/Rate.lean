import Comparison.Colour.Arcs
import Comparison.WholePicture.OneArc

/-!
# The orbit completion's rate and its least positive pole `1/320`

On the eighty states with the walk `P = B/4` (rows destinations),
`Π = 𝟏𝟏ᵀ/80` and an arc mark `X`:

* `law_projection`: `PΠ = ΠP = Π² = Π`; `arc_rate_projection`: **`Π (P ∘ X) Π = ν(X) Π`** with
  **`ν(X) = (1/320) Σ_{arcs} X`**, the rate of the mark; `primitive_rate`: a single marked arc has
  `ν = 1/320` (and `WholePicture.one_arc`: it moves the critical zero by exactly that one arc of 320).
* `nat_rate_ge`, `nat_rate_eq_iff`: **among the nonnegative integral marks with a positive total, the
  least rate is `1/320`, attained exactly by one arc carrying one unit**; `real_marks_no_minimum`: for
  real marks `r X_e` the rate `r/320` has no positive minimum (the integral class is an input).
* `shared_source_projection`: if both legs fix `Π` and `ΠAΠ = νΠ`, the two-source insertion has the
  common numerator `(1 + j_t + j_g)ν` (the global Ward numerator).
* `restK`, `rest_resolvent`, `rest_det`, `rest_poles_iff`: the completed rest pencil
  `K_X(z) = z − ν(X)β`, `β = iγ₀γ₁` the plane's clock, `β² = 1`: its inverse is
  `(z − ν)⁻¹Π₊ + (z + ν)⁻¹Π₋`, `det K_X(z) = (z² − ν²)²`, and its poles are `±ν(X)`;
  `least_positive_pole`: **the least positive pole among the nonnegative integral marks is `1/320`**.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Kronecker

-- membership in the concrete finset of the 320 arcs is checked by unfolding it
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-- The walk on the eighty states, rows destinations: `P_{pq} = 1/4` when `q → p` is a step. -/
def lawQ : Matrix State State ℚ := fun p q => if Continues q p then 1 / 4 else 0

/-- The stationary projector `Π = 𝟏𝟏ᵀ/80`. -/
def PiQ : Matrix State State ℚ := fun _ _ => 1 / 80

/-- The marked walk `P ∘ X`. -/
def markedLaw (X : State → State → ℚ) : Matrix State State ℚ := fun p q => lawQ p q * X p q

/-- **The rate of a mark:** `ν(X) = (1/320) Σ_{q → p} X_{pq}`. -/
def rate (X : State → State → ℚ) : ℚ := (∑ e ∈ arcs, X e.2 e.1) / 320

theorem lawQ_row (p : State) : ∑ q, lawQ p q = 1 := by
  have h := card_predecessors p
  simp only [lawQ]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h]
  norm_num

theorem lawQ_col (q : State) : ∑ p, lawQ p q = 1 := by
  have h := card_continuations q
  simp only [lawQ]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h]
  norm_num

/-- **The stationary projector:** `PΠ = ΠP = Π² = Π`. -/
theorem law_projection : lawQ * PiQ = PiQ ∧ PiQ * lawQ = PiQ ∧ PiQ * PiQ = PiQ := by
  refine ⟨?_, ?_, ?_⟩
  · ext p q
    simp only [Matrix.mul_apply, PiQ]
    rw [← Finset.sum_mul, lawQ_row, one_mul]
  · ext p q
    simp only [Matrix.mul_apply, PiQ]
    rw [← Finset.mul_sum, lawQ_col, mul_one]
  · ext p q
    simp only [Matrix.mul_apply, PiQ, Finset.sum_const, Finset.card_univ, card_state, nsmul_eq_mul]
    norm_num

theorem sum_arcs (X : State → State → ℚ) :
    ∑ e ∈ arcs, X e.2 e.1 = ∑ p, ∑ q, if Continues q p then X p q else 0 := by
  rw [arcs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]

theorem PiQ_sandwich (M : Matrix State State ℚ) (a b : State) :
    (PiQ * M * PiQ) a b = (∑ p, ∑ q, M p q) / 6400 := by
  simp only [Matrix.mul_apply, PiQ, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The rate is the projected marked walk:** `Π (P ∘ X) Π = ν(X) Π`. -/
theorem arc_rate_projection (X : State → State → ℚ) :
    PiQ * markedLaw X * PiQ = rate X • PiQ := by
  ext a b
  rw [PiQ_sandwich]
  simp only [Matrix.smul_apply, PiQ, smul_eq_mul, rate, sum_arcs, markedLaw, lawQ]
  have h : ∑ p, ∑ q, (if Continues q p then (1 / 4 : ℚ) else 0) * X p q =
      (1 / 4) * ∑ p, ∑ q, (if Continues q p then X p q else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> ring
  rw [h]
  ring

/-- The mark of one arc `q → p`. -/
def arcMark (e : State × State) : State → State → ℚ := fun p q => if p = e.2 ∧ q = e.1 then 1 else 0

section Generic

variable (A : Finset (State × State))

/-- The rate on a set of arcs: `(1/320) Σ_{e ∈ A} X_e`. -/
def rateOn (X : State → State → ℚ) : ℚ := (∑ e ∈ A, X e.2 e.1) / 320

theorem primitive_rateOn (e : State × State) (he : e ∈ A) : rateOn A (arcMark e) = 1 / 320 := by
  rw [rateOn, Finset.sum_eq_single_of_mem e he]
  · simp [arcMark]
  · intro f _ hf
    simp only [arcMark]
    rw [if_neg]
    intro h
    apply hf
    exact Prod.ext h.2 h.1

/-- The total of a nonnegative integral mark on the arcs. -/
def natTotalOn (X : State → State → ℕ) : ℕ := ∑ e ∈ A, X e.2 e.1

theorem rateOn_nat (X : State → State → ℕ) :
    rateOn A (fun p q => (X p q : ℚ)) = (natTotalOn A X : ℚ) / 320 := by
  rw [rateOn, natTotalOn]
  push_cast
  rfl

theorem nat_rateOn_ge (X : State → State → ℕ) (h : 0 < natTotalOn A X) :
    (1 : ℚ) / 320 ≤ rateOn A (fun p q => (X p q : ℚ)) := by
  rw [rateOn_nat]
  have : (1 : ℚ) ≤ natTotalOn A X := by exact_mod_cast h
  linarith

theorem nat_rateOn_eq_iff (X : State → State → ℕ) :
    rateOn A (fun p q => (X p q : ℚ)) = 1 / 320 ↔
      ∃ e ∈ A, X e.2 e.1 = 1 ∧ ∀ f ∈ A, f ≠ e → X f.2 f.1 = 0 := by
  rw [rateOn_nat]
  have hiff : (natTotalOn A X : ℚ) / 320 = 1 / 320 ↔ natTotalOn A X = 1 := by
    constructor
    · intro h
      have : (natTotalOn A X : ℚ) = 1 := by linarith
      exact_mod_cast this
    · intro h
      rw [h]
      norm_num
  rw [hiff, natTotalOn]
  constructor
  · intro h
    have hpos : ∑ e ∈ A, X e.2 e.1 ≠ 0 := by rw [h]; exact one_ne_zero
    obtain ⟨e, he, hXe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    have hle : X e.2 e.1 ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun g : State × State => X g.2 g.1) (fun f _ => Nat.zero_le _) he
    refine ⟨e, he, by omega, fun f hf hfe => ?_⟩
    have hsub : ({e, f} : Finset (State × State)) ⊆ A := by
      intro g hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with hg | hg
      · rw [hg]; exact he
      · rw [hg]; exact hf
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun g : State × State => X g.2 g.1) hsub
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair (Ne.symm hfe), h] at h2
    omega
  · rintro ⟨e, he, h1, h0⟩
    rw [Finset.sum_eq_single_of_mem e he (fun f hf hfe => h0 f hf hfe), h1]

end Generic

/-- **The rate of a mark:** `ν(X) = (1/320) Σ_{q → p} X_{pq}` (over the 320 arcs). -/
theorem rate_eq_rateOn (X : State → State → ℚ) : rate X = rateOn arcs X := rfl

/-- **A single marked arc has the rate `1/320`.** -/
theorem primitive_rate (e : State × State) (he : e ∈ arcs) : rate (arcMark e) = 1 / 320 := by
  rw [rate_eq_rateOn]
  exact primitive_rateOn arcs e he

/-- The total of a nonnegative integral mark on the 320 arcs. -/
def natTotal (X : State → State → ℕ) : ℕ := natTotalOn arcs X

theorem natTotal_eq (X : State → State → ℕ) : natTotal X = natTotalOn arcs X := rfl

/-- **The least rate of a nonnegative integral mark is `1/320`.** -/
theorem nat_rate_ge (X : State → State → ℕ) (h : 0 < natTotal X) :
    (1 : ℚ) / 320 ≤ rate (fun p q => (X p q : ℚ)) := by
  rw [rate_eq_rateOn]
  rw [natTotal_eq] at h
  exact nat_rateOn_ge arcs X h

/-- **The rate `1/320` is attained exactly by one arc carrying one unit.** -/
theorem nat_rate_eq_iff (X : State → State → ℕ) :
    rate (fun p q => (X p q : ℚ)) = 1 / 320 ↔
      ∃ e ∈ arcs, X e.2 e.1 = 1 ∧ ∀ f ∈ arcs, f ≠ e → X f.2 f.1 = 0 := by
  rw [rate_eq_rateOn]
  exact nat_rateOn_eq_iff arcs X

/-- **Real marks have no least positive rate:** `ν(r X_e) = r/320` for every rational `r > 0`. -/
theorem real_marks_no_minimum (e : State × State) (he : e ∈ arcs) (ε : ℚ) (hε : 0 < ε) :
    ∃ r : ℚ, 0 < r ∧ rate (fun p q => r * arcMark e p q) = r / 320 ∧ r / 320 < ε := by
  refine ⟨160 * ε, by positivity, ?_, by linarith⟩
  have h := primitive_rate e he
  rw [rate] at h ⊢
  rw [← Finset.mul_sum, mul_div_assoc, h]
  ring

/-! ## The global Ward numerator -/

/-- **One numerator for both legs:** if `ΠAΠ = νΠ` and both legs fix `Π`, then
`Π A((1 + j_t)G_t + j_g G_g) Π = (1 + j_t + j_g) ν Π`. -/
theorem shared_source_projection {n : Type*} [Fintype n] [DecidableEq n]
    (p A Gt Gg : Matrix n n ℂ) (jt jg ν : ℂ)
    (ha : p * A * p = ν • p) (ht : Gt * p = p) (hg : Gg * p = p) :
    p * (A * ((1 + jt) • Gt + jg • Gg)) * p = ((1 + jt + jg) * ν) • p := by
  have h1 : p * (A * Gt) * p = ν • p := by
    rw [Matrix.mul_assoc p, Matrix.mul_assoc A, ht, ← Matrix.mul_assoc, ha]
  have h2 : p * (A * Gg) * p = ν • p := by
    rw [Matrix.mul_assoc p, Matrix.mul_assoc A, hg, ← Matrix.mul_assoc, ha]
  calc p * (A * ((1 + jt) • Gt + jg • Gg)) * p =
        (1 + jt) • (p * (A * Gt) * p) + jg • (p * (A * Gg) * p) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = ((1 + jt + jg) * ν) • p := by
          rw [h1, h2]
          module

/-! ## The completed rest pencil -/

/-- The plane's clock `β = iγ₀γ₁`. -/
noncomputable def beta : Matrix Four Four ℂ := Complex.I • (γ 0 * γ 1)

theorem beta_sq : beta * beta = 1 := by
  have h10 : γ 1 * γ 0 = -(γ 0 * γ 1) := γ_anticomm (by decide)
  rw [beta, smul_mul_smul_comm, Complex.I_mul_I]
  have : γ 0 * γ 1 * (γ 0 * γ 1) = -1 := by
    rw [show γ 0 * γ 1 * (γ 0 * γ 1) = γ 0 * (γ 1 * γ 0) * γ 1 by simp only [Matrix.mul_assoc], h10,
      Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul, γ_mul_self]
  rw [this, smul_neg, neg_smul, one_smul, neg_neg]

theorem beta_hermitian : betaᴴ = beta := by
  have h10 : γ 1 * γ 0 = -(γ 0 * γ 1) := γ_anticomm (by decide)
  rw [beta, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, γ_conjTranspose, γ_conjTranspose, h10,
    smul_neg, Complex.star_def, Complex.conj_I, neg_smul, neg_neg]

/-- The positive and negative clock projectors `Π± = (1 ± β)/2`. -/
noncomputable def clockPos : Matrix Four Four ℂ := (1 / 2 : ℂ) • (1 + beta)
noncomputable def clockNeg : Matrix Four Four ℂ := (1 / 2 : ℂ) • (1 - beta)

theorem clock_projectors :
    clockPos * clockPos = clockPos ∧ clockNeg * clockNeg = clockNeg ∧ clockPos * clockNeg = 0 ∧
      clockPos + clockNeg = 1 ∧ beta * clockPos = clockPos ∧ beta * clockNeg = -clockNeg := by
  have hb := beta_sq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [clockPos, clockNeg, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hb, smul_add, smul_sub, smul_smul] <;>
    module

/-- **The completed rest pencil** `K_X(z) = z − ν β`. -/
noncomputable def restK (ν z : ℂ) : Matrix Four Four ℂ := z • 1 - ν • beta

/-- **Its resolvent:** `K_X(z)⁻¹ = (z − ν)⁻¹ Π₊ + (z + ν)⁻¹ Π₋`; the positive pole `ν` has the
residue `Π₊`. -/
theorem rest_resolvent (ν z : ℂ) (hp : z - ν ≠ 0) (hm : z + ν ≠ 0) :
    restK ν z * ((z - ν)⁻¹ • clockPos + (z + ν)⁻¹ • clockNeg) = 1 := by
  obtain ⟨_, _, _, hsum, hbp, hbn⟩ := clock_projectors
  rw [restK, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_smul, hbp, hbn]
  rw [show z • ((z - ν)⁻¹ • clockPos + (z + ν)⁻¹ • clockNeg) -
      ν • ((z - ν)⁻¹ • clockPos + (z + ν)⁻¹ • -clockNeg) =
      ((z - ν) * (z - ν)⁻¹) • clockPos + ((z + ν) * (z + ν)⁻¹) • clockNeg by module]
  rw [mul_inv_cancel₀ hp, mul_inv_cancel₀ hm, one_smul, one_smul, hsum]

theorem beta_eq : beta = σ₂ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [beta]
  four_ext <;> simp [γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.one_apply]

/-- **The determinant of the pencil:** `det K_X(z) = (z² − ν²)²`. -/
theorem rest_det (ν z : ℂ) : (restK ν z).det = (z ^ 2 - ν ^ 2) ^ 2 := by
  have hK : restK ν z =
      (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - ν • σ₂) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [restK, beta_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd]
  rw [hK, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_fin, Matrix.det_fin_two]
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
    norm_num
  simp [σ₂]
  ring_nf
  simp only [Complex.I_sq, hI4]
  ring

/-- **The poles of the rest pencil are `±ν`.** -/
theorem rest_poles_iff (ν z : ℂ) : (restK ν z).det = 0 ↔ z = ν ∨ z = -ν := by
  rw [rest_det]
  constructor
  · intro h
    have h1 : z ^ 2 - ν ^ 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
    have h2 : (z - ν) * (z + ν) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (rfl | rfl) <;> ring

/-- **The least positive pole among the nonnegative integral marks is `1/320`:** the completed pencil of
a nonnegative integral mark with positive total has its positive pole at `ν(X) ≥ 1/320`, with equality
exactly for one arc carrying one unit. -/
theorem least_positive_pole (X : State → State → ℕ) (h : 0 < natTotal X) :
    (restK (rate (fun p q => (X p q : ℚ)) : ℂ) (rate (fun p q => (X p q : ℚ)) : ℂ)).det = 0 ∧
      (1 : ℚ) / 320 ≤ rate (fun p q => (X p q : ℚ)) ∧
      (rate (fun p q => (X p q : ℚ)) = 1 / 320 ↔
        ∃ e ∈ arcs, X e.2 e.1 = 1 ∧ ∀ f ∈ arcs, f ≠ e → X f.2 f.1 = 0) :=
  ⟨(rest_poles_iff _ _).mpr (Or.inl rfl), nat_rate_ge X h, nat_rate_eq_iff X⟩

end Comparison.GroupsContinuumLaw
