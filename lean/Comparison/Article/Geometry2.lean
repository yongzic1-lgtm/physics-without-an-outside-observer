import Comparison.Article.Commutant2
import Comparison.Elements.KeepL
import Comparison.Elements.SixDirections
import Comparison.Existence.Words

/-!
# The singlet, the comparison in every basis, and the two real sixes (Propositions 9, 11, 16)

* `kept_by_turns_iff` (**Proposition 9**): **`(U ⊗ U)v = v` for every rotation `U ∈ Sp(2)` exactly when `v ∈ ℂΩ`**;
  the rotations `γ_aγ_b` alone already force it, since their characters separate the singlet from the other fifteen
  two-spinor states. `partial_trace_singlet`: **`Tr₂ |Ω⟩⟨Ω| = (1/4) 1`**, each system alone in the mixed state `1/4`.
* `comparison_every_basis` (**Proposition 11**): for every orthonormal basis `X_α = Σ_β O_{αβ} Y_β` of
  `ℝ1 ⊕ Q` (`Y = 1, γ₀, …, γ₄`, inner product `(1/4) tr(XY)`), **`L = Σ_α X_α ⊗ X_α`**; `orthonormal_iff`:
  the family is orthonormal exactly when `O Oᵀ = 1`.
* `p1_six_iff`, `p3_six_iff` (**Proposition 16**): for `v = t₀Ω + Σ_s t_s ℓ_s`, **`p(v) = ‖v‖²` exactly when `t₀` is
  real and every `t_s` imaginary** (P1's real six), and **`(Θ ⊗ Θ)v = v` exactly when every `t` is real**
  (P3's real six); `norm_six`: `‖v‖² = |t₀|² + Σ_s |t_s|²`.
-/

namespace Comparison.Article

open Matrix hiding J
open Complex Kronecker

/-! ## Proposition 9: only the singlet is kept -/

theorem lsign_zero (u : Fin 5) : lsign u 0 = 1 := by
  simp [lsign, disagreeSet]

/-- **Proposition 9: the rotations of `Sp(2)` keep exactly the line of the singlet.** -/
theorem kept_by_turns_iff (v : Two → ℂ) :
    (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → (U ⊗ₖ U) *ᵥ v = v) ↔
      ∃ c : ℂ, v = c • Ω := by
  constructor
  · intro hv
    have hc : ∀ l : Fin 16, l ≠ 0 → star (rel l) ⬝ᵥ v = 0 := by
      intro l hl
      obtain ⟨a, b, hab, hne⟩ := characters_separate l 0 hl
      have hfix := hv _ (γγ_unitary hab) γγ_keeps_J
      have h1 : star (rel l) ⬝ᵥ (((γ a * γ b) ⊗ₖ (γ a * γ b)) *ᵥ v) =
          (lsign a l * lsign b l) * (star (rel l) ⬝ᵥ v) := by
        rw [inner_mulVec_herm _ (γγ_kron_herm a b hab), γγ_kron_rel, star_smul, smul_dotProduct,
          star_mul', lsign_real, lsign_real, smul_eq_mul]
      rw [hfix] at h1
      rw [lsign_zero, lsign_zero, mul_one] at hne
      have h2 : (1 - lsign a l * lsign b l) * (star (rel l) ⬝ᵥ v) = 0 := by
        rw [sub_mul, one_mul, ← h1, sub_self]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hne
      · exact h
    refine ⟨star (rel 0) ⬝ᵥ v, ?_⟩
    conv_lhs => rw [rel_expand v]
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [hc l hl, zero_smul]) (by simp), rel_zero]
  · rintro ⟨c, rfl⟩ U _ hJ
    rw [Matrix.mulVec_smul, (keeps_singlet_iff U).mpr hJ]

/-- **Each system alone is in the mixed state `1/4`:** `(Tr₂ |Ω⟩⟨Ω|)_{ij} = Σ_k Ω_{ik} Ω̄_{jk} = δ_{ij}/4`. -/
theorem partial_trace_singlet (i j : Four) :
    ∑ k : Four, Ω (i, k) * star (Ω (j, k)) = (1 / 4 : ℂ) * (if i = j then 1 else 0) := by
  have h := congrFun (congrFun MΩ_mul_conjTranspose i) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h
  simpa [Ω, relOf] using h

/-! ## Proposition 11: the comparison in every orthonormal basis -/

/-- The six orthonormal directions of `ℝ1 ⊕ Q`: `1, γ₀, …, γ₄`. -/
def Ybasis : Fin 6 → Matrix Four Four ℂ := Fin.cons (1 : Matrix Four Four ℂ) γ

theorem trace_Y (b d : Fin 6) : (Ybasis b * Ybasis d).trace = if b = d then 4 else 0 := by
  refine Fin.cases ?_ (fun s => ?_) b <;> refine Fin.cases ?_ (fun t => ?_) d
  · simp [Ybasis, Matrix.trace_one]
  · simp only [Ybasis, Fin.cons_zero, Fin.cons_succ, one_mul, γ_trace]
    rw [if_neg (Fin.succ_ne_zero t).symm]
  · simp only [Ybasis, Fin.cons_zero, Fin.cons_succ, mul_one, γ_trace]
    rw [if_neg (Fin.succ_ne_zero s)]
  · simp only [Ybasis, Fin.cons_succ, trace_γ_mul_γ, Fin.succ_inj]

theorem L_eq_Y : L = ∑ b : Fin 6, Ybasis b ⊗ₖ Ybasis b := by
  rw [Fin.sum_univ_succ, L]
  simp [Ybasis]

/-- **Orthonormal in `(1/4) tr(XY)` exactly when the coefficients are orthogonal.** -/
theorem orthonormal_iff (O : Matrix (Fin 6) (Fin 6) ℝ) :
    (∀ a c : Fin 6, (1 / 4 : ℂ) * ((∑ b, (O a b : ℂ) • Ybasis b) * (∑ d, (O c d : ℂ) • Ybasis d)).trace =
      if a = c then 1 else 0) ↔ O * Oᵀ = 1 := by
  have key : ∀ a c : Fin 6, (1 / 4 : ℂ) *
      ((∑ b, (O a b : ℂ) • Ybasis b) * (∑ d, (O c d : ℂ) • Ybasis d)).trace = ((O * Oᵀ) a c : ℝ) := by
    intro a c
    have hexp : (∑ b, (O a b : ℂ) • Ybasis b) * (∑ d, (O c d : ℂ) • Ybasis d) =
        ∑ b, ∑ d, ((O a b : ℂ) * (O c d : ℂ)) • (Ybasis b * Ybasis d) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hexp, Matrix.trace_sum]
    simp only [Matrix.trace_sum, Matrix.trace_smul, trace_Y, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  constructor
  · intro h
    ext a c
    have := h a c
    rw [key] at this
    rw [Matrix.one_apply]
    split_ifs at this ⊢ with hac
    · exact_mod_cast this
    · exact_mod_cast this
  · intro h a c
    rw [key, h, Matrix.one_apply]
    split_ifs <;> simp

theorem sum_kron {ι : Type*} (s : Finset ι) (A : ι → Matrix Four Four ℂ) (B : Matrix Four Four ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kron_sum {ι : Type*} (s : Finset ι) (A : Matrix Four Four ℂ) (B : ι → Matrix Four Four ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

/-- **Proposition 11: `L = Σ_α X_α ⊗ X_α` for every orthonormal basis of `ℝ1 ⊕ Q`.** -/
theorem comparison_every_basis (O : Matrix (Fin 6) (Fin 6) ℝ)
    (hO : ∀ a c : Fin 6, (1 / 4 : ℂ) *
      ((∑ b, (O a b : ℂ) • Ybasis b) * (∑ d, (O c d : ℂ) • Ybasis d)).trace = if a = c then 1 else 0) :
    L = ∑ a, (∑ b, (O a b : ℂ) • Ybasis b) ⊗ₖ (∑ d, (O a d : ℂ) • Ybasis d) := by
  have h1 : O * Oᵀ = 1 := (orthonormal_iff O).mp hO
  have h2 : Oᵀ * O = 1 := mul_eq_one_comm.mp h1
  have hcol : ∀ b d : Fin 6, ∑ a, (O a b : ℂ) * (O a d : ℂ) = if b = d then 1 else 0 := by
    intro b d
    have := congrFun (congrFun h2 b) d
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    have h' : ((∑ a, O a b * O a d : ℝ) : ℂ) = ((if b = d then 1 else 0 : ℝ) : ℂ) := by rw [this]
    push_cast at h'
    rw [h']
    split_ifs <;> simp
  rw [L_eq_Y]
  have e : ∀ a, (∑ b, (O a b : ℂ) • Ybasis b) ⊗ₖ (∑ d, (O a d : ℂ) • Ybasis d) =
      ∑ b, ∑ d, ((O a b : ℂ) * (O a d : ℂ)) • (Ybasis b ⊗ₖ Ybasis d) := by
    intro a
    rw [sum_kron]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [kron_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hcol, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-! ## Proposition 16: the two real sixes as sets -/

/-- The six antisymmetric two-spinor states: the singlet and the five vector states. -/
def six (a : Fin 6) : Fin 16 := Fin.castLE (by norm_num) a

theorem six_injective : Function.Injective six := by
  intro a b h
  simpa [six, Fin.ext_iff] using h

/-- **`‖v‖² = |t₀|² + Σ_s |t_s|²`** for `v = Σ_a t_a e_a` on the six. -/
theorem norm_six (t : Fin 6 → ℂ) :
    star (∑ a, t a • rel (six a)) ⬝ᵥ (∑ a, t a • rel (six a)) = ∑ a, ((Complex.normSq (t a) : ℝ) : ℂ) := by
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dotProduct_sum]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, rel_inner, six_injective.eq_iff, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Complex.normSq_eq_conj_mul_self]
  simp [Complex.star_def, mul_comm]

/-- **P1's real six as a set:** `t₀² − Σ t_s² = |t₀|² + Σ |t_s|²` exactly when `t₀` is real and every `t_s`
imaginary. -/
theorem p1_six_iff (t₀ : ℂ) (t : Fin 5 → ℂ) :
    t₀ ^ 2 - ∑ s, t s ^ 2 = ((Complex.normSq t₀ + ∑ s, Complex.normSq (t s) : ℝ) : ℂ) ↔
      t₀.im = 0 ∧ ∀ s, (t s).re = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re, sq, Complex.mul_re,
      Complex.normSq_apply] at hre
    have hs : ∀ s, 0 ≤ (t s).re * (t s).re := fun s => mul_self_nonneg _
    have hsum : ∑ s, (t s).re * (t s).re = 0 := by
      have e : ∑ s, ((t s).re * (t s).re - (t s).im * (t s).im) =
          ∑ s, (t s).re * (t s).re - ∑ s, (t s).im * (t s).im := Finset.sum_sub_distrib ..
      have e2 : ∑ s, ((t s).re * (t s).re + (t s).im * (t s).im) =
          ∑ s, (t s).re * (t s).re + ∑ s, (t s).im * (t s).im := Finset.sum_add_distrib
      rw [e, e2] at hre
      have := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) => hs s)
      nlinarith [mul_self_nonneg t₀.im]
    have h0 : t₀.im * t₀.im = 0 := by
      have e : ∑ s, ((t s).re * (t s).re - (t s).im * (t s).im) =
          ∑ s, (t s).re * (t s).re - ∑ s, (t s).im * (t s).im := Finset.sum_sub_distrib ..
      have e2 : ∑ s, ((t s).re * (t s).re + (t s).im * (t s).im) =
          ∑ s, (t s).re * (t s).re + ∑ s, (t s).im * (t s).im := Finset.sum_add_distrib
      rw [e, e2, hsum] at hre
      nlinarith [mul_self_nonneg t₀.im]
    refine ⟨mul_self_eq_zero.mp h0, fun s => ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => hs s)).mp hsum s
      (Finset.mem_univ s)
    exact mul_self_eq_zero.mp this
  · rintro ⟨h0, hs⟩
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re, sq, Complex.mul_re,
        Complex.normSq_apply, h0, hs]
      simp only [mul_zero, sub_zero, zero_mul, zero_sub, add_zero, zero_add]
      rw [Finset.sum_neg_distrib]
      ring
    · simp only [Complex.sub_im, Complex.im_sum, Complex.ofReal_im, sq, Complex.mul_im, h0, hs]
      simp

/-- The quaternionic structure on two systems, `Θ ⊗ Θ : w ↦ (J ⊗ J) w̄`. -/
noncomputable def thetaTwo (w : Two → ℂ) : Two → ℂ := (J ⊗ₖ J) *ᵥ star w

theorem star_relOf (M : Matrix Four Four ℂ) : star (relOf M) = relOf (M.map star) := by
  ext ⟨x, y⟩
  simp [relOf]

theorem map_star_mul (M N : Matrix Four Four ℂ) : (M * N).map star = M.map star * N.map star := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply, star_sum, star_mul']

theorem MΩ_map_star : MΩ.map star = MΩ := by
  ext i j
  have hij := congrFun (congrFun J_map_star i) j
  simp only [Matrix.map_apply] at hij
  simp only [MΩ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hij]
  congr 1
  simp

theorem J_MΩ_J : J * MΩ * Jᵀ = MΩ := by
  rw [MΩ, Matrix.mul_smul, Matrix.smul_mul, J_mul_J, J_transpose]
  simp

/-- `Θ ⊗ Θ` keeps the singlet and the five vector states. -/
theorem thetaTwo_six (a : Fin 6) : thetaTwo (rel (six a)) = rel (six a) := by
  rw [thetaTwo, rel_eq_relOf, star_relOf, kron_mulVec_relOf]
  congr 1
  refine Fin.cases ?_ (fun s => ?_) a
  · have : relOp (six 0) = 1 := by simp [six, relOp]
    rw [this, Matrix.one_mul, MΩ_map_star, J_MΩ_J]
  · have : relOp (six s.succ) = γ s := by
      fin_cases s <;> simp [six, relOp]
    rw [this, map_star_mul, MΩ_map_star, ← Matrix.mul_assoc, ← γ_mul_J, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Matrix.mul_assoc J, J_MΩ_J]

/-- **P3's real six as a set:** `(Θ ⊗ Θ)v = v` exactly when every coordinate is real. -/
theorem p3_six_iff (t : Fin 6 → ℂ) :
    thetaTwo (∑ a, t a • rel (six a)) = ∑ a, t a • rel (six a) ↔ ∀ a, (t a).im = 0 := by
  have hT : thetaTwo (∑ a, t a • rel (six a)) = ∑ a, star (t a) • rel (six a) := by
    rw [thetaTwo, star_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_smul, Matrix.mulVec_smul]
    have := thetaTwo_six a
    rw [thetaTwo] at this
    rw [this]
  have hcoef : ∀ (c : Fin 6 → ℂ) (b : Fin 6), star (rel (six b)) ⬝ᵥ (∑ a, c a • rel (six a)) = c b := by
    intro c b
    rw [dotProduct_sum]
    simp only [dotProduct_smul, rel_inner, six_injective.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hT]
  constructor
  · intro h a
    have := congrArg (fun w => star (rel (six a)) ⬝ᵥ w) h
    simp only [hcoef] at this
    exact Complex.conj_eq_iff_im.mp this
  · intro h
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_eq_iff_im.mpr (h a)]

end Comparison.Article
