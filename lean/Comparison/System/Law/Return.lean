import Comparison.System.Postulates
import Comparison.Existence.Return
import Comparison.Existence.Excursion
import Comparison.Existence.IharaBass

/-!
# The proof system, the law: Proposition 55, the excursion is the law's return

The walk's own returns, counted on the walks:

* `retCount n`, `sRetCount n`: the reduced words of length `n` that end at the start's vertex, without and with
  the Clifford sign; `wordSum_transitionMat_zero`, `wordSum_lineOnRel_singlet`: **they are the diagonal entries
  `(N_n)_{∅∅}` and `⟨Ω, N_nΩ⟩` of the sums `N_n = Σ Γ_{t_n}⋯Γ_{t_1}` over the reduced words** (the lemma of five
  involutions, `Existence/Return.lean`).
* `pSeq`, `wordSum_eigen`, `pSeq_series`: on an eigenvector of `A = Σ_tΓ_t` with eigenvalue `λ`, `N_n` acts by
  `p_n(λ)`, and `Σ_n p_n(λ) uⁿ · (1 + 4u² − λu) = 1 − u²`.
* `countSeries_plus`, `countSeries_minus`: **`Σ_n (N_n)_{∅∅} uⁿ = (1 − u²)·(1/16)Σ_λ m_λ/(1 + 4u² − λu)`** with
  `λ = 5, 1, −3` (`m_λ = 1, 10, 5`) and **`Σ_n ⟨Ω, N_nΩ⟩ uⁿ = (1 − u²)(1 + 4u²)/(1 + 3u² + 16u⁴)`**, as formal
  power series;
* `resolvent_plus`, `resolvent_minus`: **the entries of the resolvents themselves**:
  `((1 + 4u²) − uA₊)⁻¹_{∅∅} = (1/16)Σ_λ m_λ/(1 + 4u² − λu)`,
  `⟨Ω|((1 + 4u²) − uA₋)⁻¹|Ω⟩ = (1 + 4u²)/(1 + 3u² + 16u⁴)`;
* `returns_series_plus`, `returns_series_minus`: **the returns renew to the excursion:** with `R±(z) = Σ_n r±_n zⁿ`,
  `r_0 = 1`, `r_n = (returns of length n)/(5·4ⁿ⁻¹)`: `R₊(1 − F) = 1`, `F = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`, and
  `R₋(1 − Φ) = 1`, `Φ = −z⁴/(16 + 3z²)`; and `R± = 1 + (4/5)[(1 − u²)⟨Ω|((1 + 4u²) − uA±)⁻¹|Ω⟩ − 1]`, `u = z/4`;
* `prop_55`: Proposition 55 as one statement.
-/

open Matrix Comparison PowerSeries
open scoped Kronecker

namespace Comparison.System

namespace Law

/-! ## The scalar sequence of the lemma of five involutions -/

/-- `p₀ = 1`, `p₁ = λ`, `p₂ = λ² − 5`, `p_{n+3} = λ p_{n+2} − 4 p_{n+1}`. -/
def pSeq (lam : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam
  | n + 2 => lam * pSeq lam (n + 1) - (if n = 0 then 5 else 4) * pSeq lam n

/-- **On an eigenvector of `A = Σ_t Γ_t` the word sums act by `p_n(λ)`.** -/
theorem wordSum_eigen {V : Type*} [Fintype V] [DecidableEq V] (Γ : Fin 5 → Matrix V V ℂ)
    (hΓ : ∀ t, Γ t * Γ t = 1) (v : V → ℂ) (lam : ℂ) (hv : (∑ t, Γ t) *ᵥ v = lam • v) :
    ∀ n, wordSum Γ n *ᵥ v = pSeq lam n • v := by
  have key : ∀ n, wordSum Γ n *ᵥ v = pSeq lam n • v ∧
      wordSum Γ (n + 1) *ᵥ v = pSeq lam (n + 1) • v := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [wordSum_zero, Matrix.one_mulVec]; simp [pSeq]
      · rw [wordSum_one, hv]; simp [pSeq]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hrec := wordSum_rec Γ hΓ n
      have e : wordSum Γ (n + 2) = (∑ t, Γ t) * wordSum Γ (n + 1) -
          (((if n = 0 then (5 : ℕ) else 4 : ℕ) : ℂ)) • wordSum Γ n := by
        rw [hrec, Nat.cast_smul_eq_nsmul]
        abel
      rw [e, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih.2, Matrix.mulVec_smul, hv, Matrix.smul_mulVec,
        ih.1, smul_smul, smul_smul, ← sub_smul]
      congr 1
      simp only [pSeq]
      split_ifs <;> push_cast <;> ring
  exact fun n => (key n).1

/-- **The generating function of `p_n(λ)`:** `Σ_n p_n(λ)uⁿ · (1 + 4u² − λu) = 1 − u²`. -/
theorem pSeq_series (lam : ℂ) :
    PowerSeries.mk (pSeq lam) * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2 -
      PowerSeries.C lam * PowerSeries.X) = 1 - PowerSeries.X ^ 2 := by
  ext n
  have e1 : PowerSeries.mk (pSeq lam) * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2 -
      PowerSeries.C lam * PowerSeries.X) = PowerSeries.mk (pSeq lam) +
      PowerSeries.C 4 * (PowerSeries.mk (pSeq lam) * PowerSeries.X ^ 2) -
      PowerSeries.C lam * (PowerSeries.mk (pSeq lam) * PowerSeries.X ^ 1) := by ring
  rw [e1, map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, map_sub,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp [pSeq]
  · simp [pSeq]
  · simp [pSeq]; ring
  · simp only [PowerSeries.coeff_mk, show ¬ (n + 3 = 0) from by omega,
      show ¬ (n + 3 = 2) from by omega, show 2 ≤ n + 3 from by omega, show 1 ≤ n + 3 from by omega,
      ↓reduceIte, Nat.add_sub_cancel, show n + 3 - 2 = n + 1 from by omega,
      show n + 3 - 1 = n + 2 from by omega]
    simp only [pSeq, show n + 1 ≠ 0 from by omega, ↓reduceIte]
    ring

/-! ## The returns of the walk, counted on the walks -/

/-- The walks of length `n` at the start's vertex. -/
def returns (n : ℕ) : Finset (List (Fin 5)) := (words n).filter fun w => Reduced w ∧ relOfWord w = 0

/-- Their number. -/
def retCount (n : ℕ) : ℕ := (returns n).card

/-- Their number with the Clifford sign of each. -/
def sRetCount (n : ℕ) : ℤ := ∑ w ∈ returns n, coef w

theorem transitionMat_prod_apply (w : List (Fin 5)) (k : Fin 16) :
    ((w.map transitionMat).prod) k 0 = if k = relOfWord w then 1 else 0 := by
  induction w generalizing k with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_apply]
    rfl
  | cons t w ih =>
    rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Finset.sum_eq_single (transition t k)]
    · rw [ih, relOfWord_cons]
      simp only [transitionMat, transitionMatZ, Matrix.map_apply, Matrix.of_apply, transition_transition, ↓reduceIte,
        eq_intCast, Int.cast_one, one_mul]
      by_cases h : k = transition t (relOfWord w)
      · rw [if_pos h, if_pos]
        rw [h, transition_transition]
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        rw [← h', transition_transition]
    · intro j _ hj
      simp only [transitionMat, transitionMatZ, Matrix.map_apply, Matrix.of_apply]
      have : ¬ k = transition t j := fun h => hj (by rw [h, transition_transition])
      simp [this]
    · simp

/-- **The unsigned returns are the diagonal entry of the word sums:** `(N_n)_{∅∅} = retCount n`. -/
theorem wordSum_transitionMat_zero (n : ℕ) : wordSum transitionMat n 0 0 = (retCount n : ℂ) := by
  rw [wordSum, Matrix.sum_apply, retCount, returns, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hr : Reduced w
  · rw [if_pos hr, transitionMat_prod_apply]
    by_cases h0 : relOfWord w = 0
    · simp [hr, h0]
    · simp [hr, h0, Ne.symm h0]
  · simp [hr]

theorem lineOnRel_prod (w : List (Fin 5)) :
    (w.map lineOnRel).prod = (w.map γ).prod ⊗ₖ (1 : Matrix Four Four ℂ) := by
  induction w with
  | nil => simp [Matrix.one_kronecker_one]
  | cons t w ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, lineOnRel,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem singlet_rel (k : Fin 16) : star Ω ⬝ᵥ rel k = if k = 0 then 1 else 0 := by
  rw [← rel_zero, rel_inner]
  by_cases h : k = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The signed returns are the singlet's entry of the word sums:** `⟨Ω, N_nΩ⟩ = sRetCount n`. -/
theorem wordSum_lineOnRel_singlet (n : ℕ) :
    star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω) = (sRetCount n : ℂ) := by
  rw [wordSum, Matrix.sum_mulVec, dotProduct_sum, sRetCount, returns, Finset.sum_filter,
    Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hr : Reduced w
  · rw [if_pos hr, lineOnRel_prod, history_rel, dotProduct_smul, singlet_rel, smul_eq_mul]
    by_cases h0 : relOfWord w = 0
    · simp [hr, h0]
    · simp [hr, h0]
  · simp [hr]

/-! ## The generating functions of the word sums -/

/-- The sum over the sixteen characters, by the walk's eigenvalue: `5`, then `−3` five times, `1` ten times. -/
theorem sum_charValue (f : ℂ → ℂ) :
    ∑ l : Fin 16, f ((charValue l : ℤ) : ℂ) = f 5 + 5 * f (-3) + 10 * f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, charValue]
  simp [disagreeSet]
  norm_num
  ring

theorem charTable_row_col : ∀ l : Fin 16, charTable 0 l = 1 ∧ charTable l 0 = 1 := by decide

/-- **The singlet's entry of the unsigned word sums:** `(N_n)_{∅∅} = (1/16)[p_n(5) + 5p_n(−3) + 10p_n(1)]`. -/
theorem wordSum_transitionMat_spectral (n : ℕ) :
    wordSum transitionMat n 0 0 = (1 / 16) * (pSeq 5 n + 5 * pSeq (-3) n + 10 * pSeq 1 n) := by
  -- the columns of the character table are eigenvectors
  have hcol : ∀ l : Fin 16, (∑ t, transitionMat t) *ᵥ (fun x => charTableC x l) =
      ((charValue l : ℤ) : ℂ) • (fun x => charTableC x l) := by
    intro l
    funext x
    have := congrFun (congrFun adjacency_mul_charTable_C x) l
    simp only [Matrix.mul_diagonal] at this
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [← Matrix.mul_apply, this, mul_comm]
  have hW : ∀ l : Fin 16, wordSum transitionMat n *ᵥ (fun x => charTableC x l) =
      pSeq ((charValue l : ℤ) : ℂ) n • (fun x => charTableC x l) := fun l =>
    wordSum_eigen transitionMat transitionMat_mul_self _ _ (hcol l) n
  -- the vertex `∅` is the mean of the columns
  have he : (fun x : Fin 16 => if x = 0 then (1 : ℂ) else 0) =
      (1 / 16 : ℂ) • ∑ l : Fin 16, (fun x => charTableC x l) := by
    funext x
    have h := congrFun (congrFun charTableC_mul_self x) 0
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    have hl : ∀ l : Fin 16, charTableC l 0 = 1 := by
      intro l
      simp [charTableC, (charTable_row_col l).2]
    simp only [hl, mul_one] at h
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [h]
    split_ifs <;> norm_num
  have h0 : wordSum transitionMat n 0 0 = (wordSum transitionMat n *ᵥ fun x => if x = 0 then (1 : ℂ) else 0) 0 := by
    simp [Matrix.mulVec, dotProduct]
  rw [h0, he, Matrix.mulVec_smul, Matrix.mulVec_sum]
  simp only [hW, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hr : ∀ l : Fin 16, charTableC 0 l = 1 := by
    intro l
    simp [charTableC, (charTable_row_col l).1]
  simp only [hr, mul_one]
  rw [sum_charValue (fun lam => pSeq lam n)]

/-- `⟨Ω, A₋Ω⟩ = 0`: no line keeps the singlet. -/
theorem singlet_Aminus_singlet : star Ω ⬝ᵥ ((∑ t, lineOnRel t) *ᵥ Ω) = 0 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [← rel_zero, lineOnRel, line_moves_rel, dotProduct_smul, rel_inner]
  simp [Ne.symm (transition_ne t 0)]

/-- A square root of five in `ℂ`. -/
noncomputable def sq5 : ℂ := (Real.sqrt 5 : ℂ)

theorem sq5_sq : sq5 ^ 2 = 5 := by
  rw [sq5, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sq5_ne : sq5 ≠ 0 := by
  intro h
  have := sq5_sq
  rw [h] at this
  norm_num at this

/-- The eigenvectors of `A₋` through the singlet: `v± = Ω ± A₋Ω/√5`. -/
noncomputable def vPlus : Two → ℂ := Ω + (1 / sq5) • ((∑ t, lineOnRel t) *ᵥ Ω)

noncomputable def vMinus : Two → ℂ := Ω - (1 / sq5) • ((∑ t, lineOnRel t) *ᵥ Ω)

theorem h5div : (1 / sq5) * 5 = sq5 := by
  rw [← sq5_sq]
  field_simp [sq5_ne]

theorem AA_singlet : (∑ t, lineOnRel t) *ᵥ ((∑ t, lineOnRel t) *ᵥ Ω) = (5 : ℂ) • Ω := by
  rw [Matrix.mulVec_mulVec, Aminus_sq, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem vPlus_eigen : (∑ t, lineOnRel t) *ᵥ vPlus = sq5 • vPlus := by
  rw [vPlus, Matrix.mulVec_add, Matrix.mulVec_smul, AA_singlet, smul_smul, h5div, smul_add, smul_smul,
    mul_one_div_cancel sq5_ne, one_smul, add_comm]

theorem vMinus_eigen : (∑ t, lineOnRel t) *ᵥ vMinus = (-sq5) • vMinus := by
  rw [vMinus, Matrix.mulVec_sub, Matrix.mulVec_smul, AA_singlet, smul_smul, h5div, smul_sub, smul_smul,
    neg_mul, mul_one_div_cancel sq5_ne, neg_smul, neg_smul, one_smul]
  abel

theorem singlet_eq_mean : Ω = (1 / 2 : ℂ) • (vPlus + vMinus) := by
  funext x
  simp only [vPlus, vMinus, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The singlet's entry of the signed word sums:** `⟨Ω, N_nΩ⟩ = [p_n(√5) + p_n(−√5)]/2`. -/
theorem wordSum_lineOnRel_spectral (n : ℕ) :
    star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω) = (pSeq sq5 n + pSeq (-sq5) n) / 2 := by
  have hWp := wordSum_eigen lineOnRel lineOnRel_mul_self vPlus sq5 vPlus_eigen n
  have hWm := wordSum_eigen lineOnRel lineOnRel_mul_self vMinus (-sq5) vMinus_eigen n
  have hdp : star Ω ⬝ᵥ vPlus = 1 := by
    rw [vPlus, dotProduct_add, dotProduct_smul, Ω_norm, singlet_Aminus_singlet, smul_zero, add_zero]
  have hdm : star Ω ⬝ᵥ vMinus = 1 := by
    rw [vMinus, dotProduct_sub, dotProduct_smul, Ω_norm, singlet_Aminus_singlet, smul_zero, sub_zero]
  have hWΩ : wordSum lineOnRel n *ᵥ Ω =
      (1 / 2 : ℂ) • (pSeq sq5 n • vPlus + pSeq (-sq5) n • vMinus) := by
    conv_lhs => rw [singlet_eq_mean]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hWp, hWm]
  rw [hWΩ, dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, hdp, hdm]
  simp only [smul_eq_mul, mul_one]
  ring

/-- The grade factor as a power series, `k_λ(u) = 1 + 4u² − λu`. -/
noncomputable def kSer (lam : ℂ) : PowerSeries ℂ :=
  1 + PowerSeries.C 4 * PowerSeries.X ^ 2 - PowerSeries.C lam * PowerSeries.X

/-- **The unsigned word sums' series:** `Σ (N_n)_{∅∅}uⁿ · k₅k₋₃k₁ = (1 − u²)(k₋₃k₁ + 5k₅k₁ + 10k₅k₋₃)/16`. -/
theorem countSeries_plus :
    PowerSeries.mk (fun n => wordSum transitionMat n 0 0) * (kSer 5 * kSer (-3) * kSer 1) =
      PowerSeries.C (1 / 16) * (1 - PowerSeries.X ^ 2) *
        (kSer (-3) * kSer 1 + PowerSeries.C 5 * (kSer 5 * kSer 1) +
          PowerSeries.C 10 * (kSer 5 * kSer (-3))) := by
  have e : PowerSeries.mk (fun n => wordSum transitionMat n 0 0) =
      PowerSeries.C (1 / 16) * (PowerSeries.mk (pSeq 5) + PowerSeries.C 5 * PowerSeries.mk (pSeq (-3)) +
        PowerSeries.C 10 * PowerSeries.mk (pSeq 1)) := by
    ext n
    simp only [PowerSeries.coeff_mk, wordSum_transitionMat_spectral, PowerSeries.coeff_C_mul, map_add]
  have g5 := pSeq_series 5
  have g3 := pSeq_series (-3)
  have g1 := pSeq_series 1
  change PowerSeries.mk (pSeq 5) * kSer 5 = 1 - PowerSeries.X ^ 2 at g5
  change PowerSeries.mk (pSeq (-3)) * kSer (-3) = 1 - PowerSeries.X ^ 2 at g3
  change PowerSeries.mk (pSeq 1) * kSer 1 = 1 - PowerSeries.X ^ 2 at g1
  rw [e]
  linear_combination (PowerSeries.C (1 / 16) * (kSer (-3) * kSer 1)) * g5 +
    (PowerSeries.C (1 / 16) * PowerSeries.C 5 * (kSer 5 * kSer 1)) * g3 +
    (PowerSeries.C (1 / 16) * PowerSeries.C 10 * (kSer 5 * kSer (-3))) * g1

/-- **The signed word sums' series:** `Σ ⟨Ω, N_nΩ⟩uⁿ · (1 + 3u² + 16u⁴) = (1 − u²)(1 + 4u²)`. -/
theorem countSeries_minus :
    PowerSeries.mk (fun n => star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) *
        (1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C 16 * PowerSeries.X ^ 4) =
      (1 - PowerSeries.X ^ 2) * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2) := by
  have e : PowerSeries.mk (fun n => star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) =
      PowerSeries.C (1 / 2) * (PowerSeries.mk (pSeq sq5) + PowerSeries.mk (pSeq (-sq5))) := by
    ext n
    simp only [PowerSeries.coeff_mk, wordSum_lineOnRel_spectral, PowerSeries.coeff_C_mul, map_add]
    ring
  have gp := pSeq_series sq5
  have gm := pSeq_series (-sq5)
  have hk : kSer sq5 * kSer (-sq5) =
      1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C 16 * PowerSeries.X ^ 4 := by
    simp only [kSer, map_neg]
    have h5 : PowerSeries.C sq5 * PowerSeries.C sq5 = (PowerSeries.C 5 : PowerSeries ℂ) := by
      rw [← map_mul, ← sq, sq5_sq]
    have h3 : (PowerSeries.C 3 : PowerSeries ℂ) = PowerSeries.C 4 + PowerSeries.C 4 - PowerSeries.C 5 := by
      rw [← map_add, ← map_sub]; norm_num
    have h16 : (PowerSeries.C 16 : PowerSeries ℂ) = PowerSeries.C 4 * PowerSeries.C 4 := by
      rw [← map_mul]; norm_num
    rw [h3, h16]
    linear_combination (-(PowerSeries.X : PowerSeries ℂ) ^ 2) * h5
  change PowerSeries.mk (pSeq sq5) * kSer sq5 = 1 - PowerSeries.X ^ 2 at gp
  change PowerSeries.mk (pSeq (-sq5)) * kSer (-sq5) = 1 - PowerSeries.X ^ 2 at gm
  rw [← hk, e]
  have h4 : kSer sq5 + kSer (-sq5) = PowerSeries.C 2 * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2) := by
    simp only [kSer, map_neg]
    have h2 : (PowerSeries.C 2 : PowerSeries ℂ) = 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add]; norm_num
    rw [h2]
    ring
  have hc : (PowerSeries.C (1 / 2) : PowerSeries ℂ) * PowerSeries.C 2 = 1 := by
    rw [← map_mul]; norm_num
  linear_combination (PowerSeries.C (1 / 2) * kSer (-sq5)) * gp +
    (PowerSeries.C (1 / 2) * kSer sq5) * gm + (PowerSeries.C (1 / 2) * (1 - PowerSeries.X ^ 2)) * h4 +
    ((1 - PowerSeries.X ^ 2) * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2)) * hc


/-! ## The resolvents at the singlet -/

/-- **The resolvent of the signed operator at the singlet:**
`⟨Ω|((1 + 4u²) − uA₋)⁻¹|Ω⟩ = (1 + 4u²)/(1 + 3u² + 16u⁴)`. -/
theorem resolvent_minus (u : ℂ) (hu : 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0) :
    star Ω ⬝ᵥ ((((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t)⁻¹) *ᵥ Ω) =
      (1 + 4 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4) := by
  have hA2 : (∑ t, lineOnRel t) * (∑ t, lineOnRel t) = (5 : ℂ) • 1 := Aminus_sq
  have hprod : ((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t) *
      ((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) + u • ∑ t, lineOnRel t) =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) • (1 : Matrix Two Two ℂ) := by
    rw [sub_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
      smul_mul_smul_comm, hA2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    module
  have hinv : ((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t)⁻¹ =
      (1 / (1 + 3 * u ^ 2 + 16 * u ^ 4)) •
        ((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) + u • ∑ t, lineOnRel t) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, hprod, smul_smul, one_div_mul_cancel hu, one_smul]
  rw [hinv, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, Ω_norm,
    singlet_Aminus_singlet]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  field_simp

/-- **The resolvent of the walk at the singlet:**
`((1 + 4u²) − uA₊)⁻¹_{∅∅} = (1/16)[1/((1 − u)(1 − 4u)) + 10/(1 + 4u² − u) + 5/(1 + 4u² + 3u)]`,
the eigenvalues `5, 1, −3` with multiplicities `1, 10, 5`. -/
theorem resolvent_plus (u : ℂ) (h1 : (1 - u) * (1 - 4 * u) ≠ 0) (h2 : 1 + 4 * u ^ 2 - u ≠ 0)
    (h3 : 1 + 4 * u ^ 2 + 3 * u ≠ 0) :
    (((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, transitionMat t)⁻¹) 0 0 =
      (1 / 16) * (1 / ((1 - u) * (1 - 4 * u)) + 10 / (1 + 4 * u ^ 2 - u) +
        5 / (1 + 4 * u ^ 2 + 3 * u)) := by
  set d : Fin 16 → ℂ := fun l => (1 + 4 * u ^ 2) - u * ((charValue l : ℤ) : ℂ) with hd
  have hd0 : ∀ l, d l ≠ 0 := by
    intro l
    have hv := charValue_values
    have : ((charValue l : ℤ) : ℂ) = 5 ∨ ((charValue l : ℤ) : ℂ) = 1 ∨ ((charValue l : ℤ) : ℂ) = -3 := by
      have hl : charValue l = 5 ∨ charValue l = 1 ∨ charValue l = -3 := by
        revert l; decide
      rcases hl with h | h | h <;> simp [h]
    rcases this with h | h | h <;> simp only [hd, h]
    · intro h0; apply h1; linear_combination h0
    · intro h0; apply h2; linear_combination h0
    · intro h0; apply h3; linear_combination h0
  have hK : ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, transitionMat t) * charTableC =
      charTableC * Matrix.diagonal d := by
    rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, adjacency_mul_charTable_C]
    ext x l
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul, hd]
    ring
  have hinv : ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, transitionMat t)⁻¹ =
      (1 / 16 : ℂ) • (charTableC * Matrix.diagonal (fun l => (d l)⁻¹) * charTableC) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hK, Matrix.mul_assoc charTableC,
      Matrix.diagonal_mul_diagonal]
    have : (fun l => d l * (d l)⁻¹) = fun _ => (1 : ℂ) := by
      funext l; exact mul_inv_cancel₀ (hd0 l)
    rw [this, Matrix.diagonal_one, Matrix.mul_one, charTableC_mul_self, smul_smul]
    norm_num
  rw [hinv, Matrix.smul_apply, smul_eq_mul]
  have hr : ∀ l : Fin 16, charTableC 0 l = 1 := by
    intro l
    simp [charTableC, (charTable_row_col l).1]
  have hc : ∀ l : Fin 16, charTableC l 0 = 1 := by
    intro l
    simp [charTableC, (charTable_row_col l).2]
  have e : (charTableC * Matrix.diagonal (fun l => (d l)⁻¹) * charTableC) 0 0 = ∑ l, (d l)⁻¹ := by
    simp only [Matrix.mul_apply, Matrix.mul_diagonal, hr, hc, one_mul, mul_one]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l]
    · simp [Matrix.diagonal_apply]
    · intro b _ hb
      simp [Matrix.diagonal_apply, hb]
    · simp
  rw [e, hd]
  rw [sum_charValue (fun lam => ((1 + 4 * u ^ 2) - u * lam)⁻¹)]
  have e5 : (1 + 4 * u ^ 2) - u * 5 = (1 - u) * (1 - 4 * u) := by ring
  rw [e5]
  field_simp
  ring

/-! ## The returns renew to the excursion -/

/-- **The returns of the walk at the step weight `z`:** `r₀ = 1`, `r_n = (count)/(5·4ⁿ⁻¹)`. -/
noncomputable def retWeight (cnt : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 1 else cnt n / (5 * 4 ^ (n - 1))

/-- `R₊(z) = Σ_n r⁺_n zⁿ`, the unsigned returns. -/
noncomputable def Rplus : PowerSeries ℂ := PowerSeries.mk (retWeight fun n => (retCount n : ℂ))

/-- `R₋(z) = Σ_n r⁻_n zⁿ`, the returns with their Clifford signs. -/
noncomputable def Rminus : PowerSeries ℂ := PowerSeries.mk (retWeight fun n => (sRetCount n : ℂ))

/-- `C n = n` for a numeral `n` (the simplifier does not see it). -/
theorem C_ofNat (k : ℕ) [k.AtLeastTwo] :
    (PowerSeries.C (OfNat.ofNat k : ℂ) : PowerSeries ℂ) = (OfNat.ofNat k : PowerSeries ℂ) :=
  map_ofNat _ k

/-- The constant coefficient of a numeral. -/
theorem cc_ofNat (k : ℕ) [k.AtLeastTwo] :
    PowerSeries.constantCoeff (OfNat.ofNat k : PowerSeries ℂ) = (OfNat.ofNat k : ℂ) :=
  map_ofNat _ k

/-- The scaled generating function: `Σ_n p_n(λ)(z/4)ⁿ · (16 + 4z² − 4λz) = 16 − z²`. -/
theorem pSeqZ_series (lam : ℂ) :
    PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq lam n) *
      (16 + 4 * PowerSeries.X ^ 2 - PowerSeries.C (4 * lam) * PowerSeries.X) =
      16 - PowerSeries.X ^ 2 := by
  set q : PowerSeries ℂ := PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq lam n) with hq
  have e1 : q * (16 + 4 * PowerSeries.X ^ 2 - PowerSeries.C (4 * lam) * PowerSeries.X) =
      PowerSeries.C 16 * q + PowerSeries.C 4 * (q * PowerSeries.X ^ 2) -
        PowerSeries.C (4 * lam) * (q * PowerSeries.X ^ 1) := by
    rw [C_ofNat 16, C_ofNat 4]
    ring
  have e2 : (16 - PowerSeries.X ^ 2 : PowerSeries ℂ) = PowerSeries.C 16 - PowerSeries.X ^ 2 := by
    rw [C_ofNat 16]
  rw [e1, e2]
  ext n
  rw [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', hq, PowerSeries.coeff_mk, map_sub,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp [pSeq]
  · simp [pSeq]
    ring
  · simp [pSeq]
    ring
  · simp only [PowerSeries.coeff_mk, show ¬ (n + 3 = 0) from by omega,
      show ¬ (n + 3 = 2) from by omega, show 2 ≤ n + 3 from by omega, show 1 ≤ n + 3 from by omega,
      ↓reduceIte, show n + 3 - 2 = n + 1 from by omega, show n + 3 - 1 = n + 2 from by omega]
    simp only [pSeq, show n + 1 ≠ 0 from by omega, ↓reduceIte]
    ring

theorem retCount_zero : retCount 0 = 1 := by decide

theorem sRetCount_zero : sRetCount 0 = 1 := by decide

/-- `5R₊ = 1 + 4·Σ_n (N_n)_{∅∅}(z/4)ⁿ`. -/
theorem Rplus_eq :
    (5 : PowerSeries ℂ) * Rplus =
      1 + 4 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * wordSum transitionMat n 0 0) := by
  ext n
  rw [PowerSeries.coeff_ofNat_mul, map_add, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_one, Rplus,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, wordSum_transitionMat_zero]
  rcases n with _ | n
  · simp [retWeight, retCount_zero] <;> norm_num
  · simp only [retWeight, Nat.add_sub_cancel, show n + 1 ≠ 0 from by omega, ↓reduceIte, zero_add]
    rw [one_div, inv_pow]
    field_simp <;> ring

/-- `5R₋ = 1 + 4·Σ_n ⟨Ω, N_nΩ⟩(z/4)ⁿ`. -/
theorem Rminus_eq :
    (5 : PowerSeries ℂ) * Rminus =
      1 + 4 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) := by
  ext n
  rw [PowerSeries.coeff_ofNat_mul, map_add, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_one, Rminus,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, wordSum_lineOnRel_singlet]
  rcases n with _ | n
  · simp [retWeight, sRetCount_zero] <;> norm_num
  · simp only [retWeight, Nat.add_sub_cancel, show n + 1 ≠ 0 from by omega, ↓reduceIte, zero_add]
    rw [one_div, inv_pow]
    field_simp <;> ring

theorem ne_zero_of_constantCoeff {f : PowerSeries ℂ} (h : PowerSeries.constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf; apply h; rw [hf, map_zero]

/-- **The unsigned returns renew to the excursion:** `R₊(z)(16 − 8z − 3z² − 3z³ − z⁴ − z⁵) = 16 − 8z − 3z² − 3z³`,
that is `R₊ = 1/(1 − F)` with `F = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`. -/
theorem returns_series_plus :
    Rplus * (16 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 -
      PowerSeries.X ^ 4 - PowerSeries.X ^ 5) =
      16 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 := by
  have hC : (16 : PowerSeries ℂ) * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * wordSum transitionMat n 0 0) =
      PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq 5 n) +
        5 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq (-3) n) +
        10 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq 1 n) := by
    ext n
    rw [PowerSeries.coeff_ofNat_mul, map_add, map_add, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_ofNat_mul]
    simp only [PowerSeries.coeff_mk]
    rw [wordSum_transitionMat_spectral]
    ring
  have g5 := pSeqZ_series 5
  have g3 := pSeqZ_series (-3)
  have g1 := pSeqZ_series 1
  have k5 : (16 + 4 * X ^ 2 - PowerSeries.C (4 * 5) * X : PowerSeries ℂ) = 16 + 4 * X ^ 2 - 20 * X := by
    rw [show (4 * 5 : ℂ) = 20 by norm_num, C_ofNat 20]
  have k3 : (16 + 4 * X ^ 2 - PowerSeries.C (4 * -3) * X : PowerSeries ℂ) = 16 + 4 * X ^ 2 + 12 * X := by
    rw [show (4 * -3 : ℂ) = -12 by norm_num, map_neg, C_ofNat 12]
    ring
  have k1 : (16 + 4 * X ^ 2 - PowerSeries.C (4 * 1) * X : PowerSeries ℂ) = 16 + 4 * X ^ 2 - 4 * X := by
    rw [show (4 * 1 : ℂ) = 4 by norm_num, C_ofNat 4]
  rw [k5] at g5
  rw [k3] at g3
  rw [k1] at g1
  have hR := Rplus_eq
  -- multiply the goal by the nonzero `1280 (4 − X)`
  have hne : (1280 * (4 - X) : PowerSeries ℂ) ≠ 0 := by
    apply ne_zero_of_constantCoeff
    rw [map_mul, map_sub, PowerSeries.constantCoeff_X, cc_ofNat 1280, cc_ofNat 4]
    norm_num
  apply mul_left_cancel₀ hne
  linear_combination (256 * (4 - X) * (16 - 8 * X - 3 * X ^ 2 - 3 * X ^ 3 - X ^ 4 - X ^ 5)) * hR +
    (64 * (4 - X) * (16 - 8 * X - 3 * X ^ 2 - 3 * X ^ 3 - X ^ 4 - X ^ 5)) * hC +
    ((16 + 4 * X ^ 2 + 12 * X) * (16 + 4 * X ^ 2 - 4 * X)) * g5 +
    (5 * (16 + 4 * X ^ 2 - 20 * X) * (16 + 4 * X ^ 2 - 4 * X)) * g3 +
    (10 * (16 + 4 * X ^ 2 - 20 * X) * (16 + 4 * X ^ 2 + 12 * X)) * g1

/-- **The signed returns renew to the signed excursion:** `R₋(z)(16 + 3z² + z⁴) = 16 + 3z²`, that is
`R₋ = 1/(1 − Φ)` with `Φ = −z⁴/(16 + 3z²)`. -/
theorem returns_series_minus :
    Rminus * (16 + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) = 16 + 3 * PowerSeries.X ^ 2 := by
  have hC : (2 : PowerSeries ℂ) *
      PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) =
      PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq sq5 n) +
        PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq (-sq5) n) := by
    ext n
    rw [PowerSeries.coeff_ofNat_mul, map_add]
    simp only [PowerSeries.coeff_mk]
    rw [wordSum_lineOnRel_spectral]
    ring
  have gp := pSeqZ_series sq5
  have gm := pSeqZ_series (-sq5)
  have km : (PowerSeries.C (4 * -sq5) : PowerSeries ℂ) = -PowerSeries.C (4 * sq5) := by
    rw [mul_neg, map_neg]
  rw [km] at gm
  have h80 : (PowerSeries.C (4 * sq5) : PowerSeries ℂ) * PowerSeries.C (4 * sq5) = 80 := by
    have h5 := sq5_sq
    rw [← map_mul, show (4 * sq5) * (4 * sq5) = (80 : ℂ) by linear_combination 16 * h5, C_ofNat 80]
  have hR := Rminus_eq
  have hne : (160 : PowerSeries ℂ) ≠ 0 := by
    apply ne_zero_of_constantCoeff
    rw [cc_ofNat 160]
    norm_num
  apply mul_left_cancel₀ hne
  linear_combination (32 * (16 + 3 * X ^ 2 + X ^ 4)) * hR + (64 * (16 + 3 * X ^ 2 + X ^ 4)) * hC +
    (4 * (16 + 4 * X ^ 2 - -PowerSeries.C (4 * sq5) * X)) * gp +
    (4 * (16 + 4 * X ^ 2 - PowerSeries.C (4 * sq5) * X)) * gm +
    (4 * X ^ 2 * (PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq sq5 n) +
      PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * pSeq (-sq5) n))) * h80

/-- `R = 1/(1 − F)`: if `R(Q − P) = Q` with `Q` invertible then `R(1 − P Q⁻¹) = 1`. -/
theorem renewal_of_series {R P Q : PowerSeries ℂ} (hQ : PowerSeries.constantCoeff Q ≠ 0)
    (h : R * (Q - P) = Q) : R * (1 - P * Q⁻¹) = 1 := by
  have hQQ : Q * Q⁻¹ = 1 := PowerSeries.mul_inv_cancel Q hQ
  calc R * (1 - P * Q⁻¹) = R * (Q - P) * Q⁻¹ := by
        rw [mul_assoc, sub_mul, hQQ]
    _ = 1 := by rw [h, hQQ]

end Law

open Comparison.System.Law

/-- **Proposition 55, the excursion is the law's return.** The walk's returns, counted on the walks (the reduced
words at the start's vertex, with or without their Clifford signs), are the entries `(N_n)_{∅∅}` and `⟨Ω, N_nΩ⟩` of
the word sums of the lemma of five involutions; their generating functions are
`Σ_n (N_n)_{∅∅}uⁿ = (1 − u²)·(1/16)Σ_λ m_λ/(1 + 4u² − λu)` and `Σ_n ⟨Ω, N_nΩ⟩uⁿ = (1 − u²)(1 + 4u²)/(1 + 3u² + 16u⁴)`
(formal power series, the denominators multiplied out), and these are `(1 − u²)` times the resolvents at the
singlet, `((1 + 4u²) − uA₊)⁻¹_{∅∅} = (1/16)Σ_λ m_λ/(1 + 4u² − λu)` and `⟨Ω|((1 + 4u²) − uA₋)⁻¹|Ω⟩ =
(1 + 4u²)/(1 + 3u² + 16u⁴)`; with `R±(z) = Σ_n r±_n zⁿ`, `r_0 = 1`, `r_n = (returns of length n)/(5·4ⁿ⁻¹)`:
`5R± = 1 + 4Σ_n c±_n(z/4)ⁿ`, that is `R± = 1 + (4/5)[(1 − u²)⟨Ω|((1 + 4u²) − uA±)⁻¹|Ω⟩ − 1]` at `u = z/4`, and
`R₊ = 1/(1 − F)`, `F = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`, `R₋ = 1/(1 − Φ)`, `Φ = −z⁴/(16 + 3z²)`, the excursion and the
signed excursion of Propositions 29 and 30 (`excursion_gf_eq`, `signed_gf_eq`).
Every candidate system: System.uniqueness. -/
theorem prop_55 :
    (∀ n, wordSum transitionMat n 0 0 = (retCount n : ℂ)) ∧
    (∀ n, star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω) = (sRetCount n : ℂ)) ∧
    PowerSeries.mk (fun n => wordSum transitionMat n 0 0) * (kSer 5 * kSer (-3) * kSer 1) =
      PowerSeries.C (1 / 16) * (1 - PowerSeries.X ^ 2) *
        (kSer (-3) * kSer 1 + PowerSeries.C 5 * (kSer 5 * kSer 1) +
          PowerSeries.C 10 * (kSer 5 * kSer (-3))) ∧
    PowerSeries.mk (fun n => star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) *
        (1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C 16 * PowerSeries.X ^ 4) =
      (1 - PowerSeries.X ^ 2) * (1 + PowerSeries.C 4 * PowerSeries.X ^ 2) ∧
    (∀ u : ℂ, (1 - u) * (1 - 4 * u) ≠ 0 → 1 + 4 * u ^ 2 - u ≠ 0 → 1 + 4 * u ^ 2 + 3 * u ≠ 0 →
      (((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, transitionMat t)⁻¹) 0 0 =
        (1 / 16) * (1 / ((1 - u) * (1 - 4 * u)) + 10 / (1 + 4 * u ^ 2 - u) +
          5 / (1 + 4 * u ^ 2 + 3 * u))) ∧
    (∀ u : ℂ, 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0 →
      star Ω ⬝ᵥ ((((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t)⁻¹) *ᵥ Ω) =
        (1 + 4 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4)) ∧
    (5 : PowerSeries ℂ) * Rplus =
      1 + 4 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * wordSum transitionMat n 0 0) ∧
    (5 : PowerSeries ℂ) * Rminus =
      1 + 4 * PowerSeries.mk (fun n => (1 / 4 : ℂ) ^ n * star Ω ⬝ᵥ (wordSum lineOnRel n *ᵥ Ω)) ∧
    Rplus * (1 - (PowerSeries.X ^ 4 + PowerSeries.X ^ 5) *
      (16 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3)⁻¹) = 1 ∧
    Rminus * (1 - (-PowerSeries.X ^ 4) * (16 + 3 * PowerSeries.X ^ 2)⁻¹) = 1 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (excursionLaw n : ℂ) * z ^ n) (excursionGF z)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (Law.Phi z)) := by
  refine ⟨wordSum_transitionMat_zero, wordSum_lineOnRel_singlet, countSeries_plus, countSeries_minus,
    resolvent_plus, resolvent_minus, Rplus_eq, Rminus_eq, ?_, ?_, excursion_gf_eq, signed_gf_eq⟩
  · refine renewal_of_series ?_ ?_
    · simp only [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X]
      rw [cc_ofNat 16, cc_ofNat 8, cc_ofNat 3]
      norm_num
    · rw [show (16 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 : PowerSeries ℂ) -
          (PowerSeries.X ^ 4 + PowerSeries.X ^ 5) = 16 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2 -
            3 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 by ring]
      exact returns_series_plus
  · refine renewal_of_series ?_ ?_
    · simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X]
      rw [cc_ofNat 16, cc_ofNat 3]
      norm_num
    · rw [show (16 + 3 * PowerSeries.X ^ 2 : PowerSeries ℂ) - -PowerSeries.X ^ 4 =
          16 + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 by ring]
      exact returns_series_minus

end Comparison.System
