import Comparison.System.Geometry.TwoThings
import Comparison.System.Geometry.Lines
import Comparison.GroupsContinuumLaw.Spin6
import Comparison.Elements.Divisions
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed

/-!
# The geometry of comparison, Book III: the six directions (Propositions 16 to 19)

* `prop_16`: the six directions are the singlet and the five vector states, orthonormal;
  `p(v) = t₀² − Σt_s²`, `‖v‖² = |t₀|² + Σ|t_s|²`; P1's real six `t₀ ∈ ℝ, t_s ∈ iℝ`, P3's real six
  every `t ∈ ℝ`.
* `prop_17`: `su(4) = sp(2) ⊕ iQ`; `SU(4) → SO(6)` onto with kernel `±1`;
  `(e^{iaγ_s} ⊗ e^{iaγ_s})Ω = cos 2a Ω + sin 2a iℓ_s`; keeping `Ω`: `Sp(2)`; keeping `L`:
  `Sp(2) ∪ i Sp(2)`; P3's division keeps the ten and moves the five.
* `prop_18`: `det X = (t₀² − |t|²)²`, `X ≥ 0 ⟺ t₀ ≥ |t|`, the edge, P3's real six `= q(P1's)`.
* `prop_19`: the square root of the sign of every division, its four solutions, the metric, the sixty-four sets.
-/

open scoped InnerProductSpace Kronecker ComplexOrder
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## The exponential of an element of square `−1` -/

section Exp

/-- **`e^{aX} = cos a + sin a X` when `X² = −1`.** -/
theorem exp_smul_of_sq (X : Matrix Four Four ℂ) (hX : X * X = -1) (a : ℝ) :
    NormedSpace.exp ((a : ℂ) • X) =
      (Real.cos a : ℂ) • (1 : Matrix Four Four ℂ) + (Real.sin a : ℂ) • X := by
  let f : ℂ →ₐ[ℝ] Matrix Four Four ℂ := Complex.liftAux X hX
  have hfz : ∀ z : ℂ, f z = (z.re : ℂ) • (1 : Matrix Four Four ℂ) + (z.im : ℂ) • X := by
    intro z
    show Complex.liftAux X hX z = _
    rw [Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one, Complex.coe_smul, Complex.coe_smul]
  have key : f (NormedSpace.exp ((a : ℂ) * Complex.I)) =
      NormedSpace.exp (f ((a : ℂ) * Complex.I)) := by
    letI : NormedRing (Matrix Four Four ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix Four Four ℂ) := Matrix.linftyOpNormedAlgebra
    exact NormedSpace.map_exp f (LinearMap.continuous_of_finiteDimensional f.toLinearMap) _
  have hfa : f ((a : ℂ) * Complex.I) = (a : ℂ) • X := by
    rw [hfz]
    simp
  rw [hfa, ← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    hfz] at key
  rw [← key]
  simp

end Exp

/-! ## Proposition 16 -/

theorem swap_conjTranspose : swapᴴ = swap := by
  ext p q
  rw [Matrix.conjTranspose_apply, ArticleStatements.swap_real, ArticleStatements.swap_symm]

theorem six_eq_castAdd (a : Fin 6) : Article.six a = Fin.castAdd 10 a := Fin.ext rfl

theorem rel_six_zero : rel (Article.six 0) = Ω := rel_zero

theorem rel_six_succ (s : Fin 5) : rel (Article.six s.succ) = (γ s ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  fin_cases s <;> rfl

theorem plane_card (i : Fin 10) : (disagreeSet (Fin.natAdd 6 i)).card = 2 := by
  revert i; decide

theorem six_card (a : Fin 6) : (disagreeSet (Article.six a)).card ≠ 2 := by
  revert a; decide

/-- **The six directions are the singlet and the five vector states.** -/
theorem mem_sixDirections_iff (v : Two → ℂ) :
    v ∈ sixDirections ↔ ∃ t : Fin 6 → ℂ, v = ∑ a, t a • rel (Article.six a) := by
  have hcoef : ∀ l : Fin 16, star (rel l) ⬝ᵥ (swap *ᵥ v) =
      (if (disagreeSet l).card = 2 then 1 else -1 : ℂ) * (star (rel l) ⬝ᵥ v) := by
    intro l
    rw [Article.inner_mulVec_herm swap swap_conjTranspose, swap_rel, swapSign]
    split_ifs <;> simp
  constructor
  · intro hv
    have hv' : swap *ᵥ v = -v := hv
    have hface : ∀ l : Fin 16, (disagreeSet l).card = 2 → star (rel l) ⬝ᵥ v = 0 := by
      intro l hl
      have h1 := hcoef l
      rw [hv', dotProduct_neg, if_pos hl, one_mul] at h1
      have : (2 : ℂ) * (star (rel l) ⬝ᵥ v) = 0 := by linear_combination -h1
      simpa using this
    refine ⟨fun a => star (rel (Article.six a)) ⬝ᵥ v, ?_⟩
    conv_lhs => rw [Article.rel_expand v]
    rw [Fin.sum_univ_add (fun l : Fin (6 + 10) => (star (rel l) ⬝ᵥ v) • rel l)]
    have h0 : ∑ i : Fin 10, (star (rel (Fin.natAdd 6 i)) ⬝ᵥ v) • rel (Fin.natAdd 6 i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hface _ (plane_card i), zero_smul]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [six_eq_castAdd]
  · rintro ⟨t, rfl⟩
    show swap *ᵥ (∑ a, t a • rel (Article.six a)) = -(∑ a, t a • rel (Article.six a))
    rw [Matrix.mulVec_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec_smul, swap_rel, swapSign, if_neg (six_card a)]
    simp

theorem relMat_sum {ι : Type*} (s : Finset ι) (f : ι → Two → ℂ) :
    relMat (∑ i ∈ s, f i) = ∑ i ∈ s, relMat (f i) := by
  ext x y
  simp [relMat, Finset.sum_apply, Matrix.sum_apply]

theorem relMat_smul (c : ℂ) (v : Two → ℂ) : relMat (c • v) = c • relMat v := by
  ext x y
  simp [relMat]

theorem relOp_six_zero : relOp (Article.six 0) = 1 := rfl

theorem relOp_six_succ (s : Fin 5) : relOp (Article.six s.succ) = γ s := by
  fin_cases s <;> rfl

theorem relMat_six (t : Fin 6 → ℂ) :
    relMat (∑ a, t a • rel (Article.six a)) =
      (-(1 / 2) : ℂ) • (t 0 • J + ∑ s : Fin 5, t s.succ • (γ s * J)) := by
  rw [relMat_sum]
  simp only [relMat_smul, rel_eq_relOf, relMat_relOf]
  rw [Fin.sum_univ_succ, relOp_six_zero]
  simp only [relOp_six_succ, MΩ, Matrix.one_mul, Matrix.mul_smul]
  rw [smul_add, Finset.smul_sum]
  congr 1
  · rw [smul_comm]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_comm]

/-- **The Pfaffian of the six:** `p(t₀Ω + Σ t_sℓ_s) = t₀² − Σ t_s²`. -/
theorem pfRel_six (t : Fin 6 → ℂ) :
    pfRel (∑ a, t a • rel (Article.six a)) = t 0 ^ 2 - ∑ s : Fin 5, t s.succ ^ 2 := by
  rw [pfRel, relMat_six, MΩ, pf_smul, pf_smul]
  have h := sign_of_time (t 0) (fun s => t s.succ)
  rw [pf_J, div_one] at h
  rw [pf_J, mul_one, h]
  have hc : ((-(1 / 2) : ℂ)) ^ 2 ≠ 0 := by norm_num
  field_simp

theorem mem_P1six_iff (t : Fin 6 → ℂ) :
    (∑ a, t a • rel (Article.six a)) ∈ P1six ↔ (t 0).im = 0 ∧ ∀ s : Fin 5, (t s.succ).re = 0 := by
  have hmem : (∑ a, t a • rel (Article.six a)) ∈ sixDirections :=
    (mem_sixDirections_iff _).mpr ⟨t, rfl⟩
  have h := Article.p1_six_iff (t 0) (fun s => t s.succ)
  have hn := Article.norm_six t
  rw [Fin.sum_univ_succ (fun a => ((Complex.normSq (t a) : ℝ) : ℂ))] at hn
  show (_ ∈ sixDirections ∧ _) ↔ _
  rw [pfRel_six, hn]
  push_cast at h ⊢
  exact ⟨fun h' => h.mp h'.2, fun h' => ⟨hmem, h.mpr h'⟩⟩

theorem mem_P3six_iff (t : Fin 6 → ℂ) :
    (∑ a, t a • rel (Article.six a)) ∈ P3six ↔ ∀ a, (t a).im = 0 := by
  have hmem : (∑ a, t a • rel (Article.six a)) ∈ sixDirections :=
    (mem_sixDirections_iff _).mpr ⟨t, rfl⟩
  show (_ ∈ sixDirections ∧ _) ↔ _
  exact ⟨fun h => (Article.p3_six_iff t).mp h.2, fun h => ⟨hmem, (Article.p3_six_iff t).mpr h⟩⟩

/-! ## Proposition 17 -/

theorem gen_inr_comm_J (f : Fin 10) : gen (Sum.inr f) * J = J * (gen (Sum.inr f)).map star := by
  have h := obs_mul_J (genIdx (Sum.inr f))
  have hp : obsParity (genIdx (Sum.inr f)) = -1 := by fin_cases f <;> rfl
  rw [hp] at h
  rw [gen, Matrix.smul_mul, h]
  have hm : (I • obs (genIdx (Sum.inr f))).map star = -I • (obs (genIdx (Sum.inr f))).map star := by
    ext i j; simp [Complex.conj_I]
  rw [hm, Matrix.mul_smul]
  simp [smul_smul]

theorem gen_inl_anticomm_J (s : Fin 5) :
    gen (Sum.inl s) * J = -(J * (gen (Sum.inl s)).map star) := by
  have h := obs_mul_J (genIdx (Sum.inl s))
  have hp : obsParity (genIdx (Sum.inl s)) = 1 := by fin_cases s <;> rfl
  rw [hp, one_smul] at h
  rw [gen, Matrix.smul_mul, h]
  have hm : (I • obs (genIdx (Sum.inl s))).map star = -I • (obs (genIdx (Sum.inl s))).map star := by
    ext i j; simp [Complex.conj_I]
  rw [hm, Matrix.mul_smul]
  simp [smul_smul]

/-- **`su(4) = sp(2) ⊕ iQ`.** -/
theorem su4_eq_sup :
    su4 = sp2 ⊔ Submodule.span ℝ (Set.range fun s : Fin 5 => gen (Sum.inl s)) ∧
    Disjoint sp2 (Submodule.span ℝ (Set.range fun s : Fin 5 => gen (Sum.inl s))) := by
  have hr : Set.range gen = Set.range (fun f : Fin 10 => gen (Sum.inr f)) ∪
      Set.range (fun s : Fin 5 => gen (Sum.inl s)) := by
    ext X
    constructor
    · rintro ⟨x, rfl⟩
      rcases x with s | f
      · exact Or.inr ⟨s, rfl⟩
      · exact Or.inl ⟨f, rfl⟩
    · rintro (⟨f, rfl⟩ | ⟨s, rfl⟩)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [su4_eq_span, hr, Submodule.span_union, sp2_eq_span]
  · rw [sp2_eq_span]
    have h := gen_linearIndependent.disjoint_span_image (s := Set.range Sum.inr)
      (t := Set.range Sum.inl) (by
        rw [Set.disjoint_iff]
        rintro x ⟨⟨f, rfl⟩, ⟨s, hs⟩⟩
        cases hs)
    rw [← Set.range_comp, ← Set.range_comp] at h
    exact h

theorem I_gamma_sq (s : Fin 5) : (I • γ s) * (I • γ s) = -1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, γ_mul_self, neg_one_smul]

/-- **`e^{iaγ_s} = cos a + i sin a γ_s`** and **`(e^{iaγ_s} ⊗ e^{iaγ_s})Ω = cos 2a Ω + sin 2a iℓ_s`.** -/
theorem exp_line_on_singlet (a : ℝ) (s : Fin 5) :
    NormedSpace.exp ((a : ℂ) • (I • γ s)) =
        (Real.cos a : ℂ) • (1 : Matrix Four Four ℂ) + (Real.sin a : ℂ) • (I • γ s) ∧
    (NormedSpace.exp ((a : ℂ) • (I • γ s)) ⊗ₖ NormedSpace.exp ((a : ℂ) • (I • γ s))) *ᵥ Ω =
      (Real.cos (2 * a) : ℂ) • Ω + (Real.sin (2 * a) : ℂ) • (I • ((γ s ⊗ₖ 1) *ᵥ Ω)) := by
  have he := exp_smul_of_sq (I • γ s) (I_gamma_sq s) a
  refine ⟨he, ?_⟩
  have hb : NormedSpace.exp ((a : ℂ) • (I • γ s)) =
      GroupsContinuumLaw.boostM (Real.cos a) (Real.sin a) (EuclideanSpace.single s 1) := by
    rw [he, GroupsContinuumLaw.boostM, GroupsContinuumLaw.Kmat, GroupsContinuumLaw.gE_single]
  rw [hb]
  exact GroupsContinuumLaw.turn_singlet a s

/-! ## Proposition 18 -/

theorem gamma_smul (c : ℝ) (t : Fin 5 → ℝ) : gamma (c • t) = (c : ℂ) • gamma t := by
  simp only [gamma, γv, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem side_posSemidef (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) : (side n).PosSemidef := by
  have hH : (side n)ᴴ = side n := (GroupsContinuumLaw.side_isQProj n hn).1
  have h := Matrix.posSemidef_conjTranspose_mul_self (side n)
  rwa [hH, side_mul_self n hn] at h

theorem norm_sq_pos {t : Fin 5 → ℝ} (ht : t ≠ 0) : 0 < ∑ s, t s ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  have hi' : t i ≠ 0 := by simpa using hi
  have h1 : 0 < t i ^ 2 := by
    rcases lt_or_gt_of_ne hi' with h | h <;> nlinarith
  have h2 : t i ^ 2 ≤ ∑ s, t s ^ 2 :=
    Finset.single_le_sum (fun s _ => sq_nonneg (t s)) (Finset.mem_univ i)
  linarith

/-- The unit line of a nonzero `t`. -/
noncomputable def unitOf (t : Fin 5 → ℝ) : Fin 5 → ℝ := (Real.sqrt (∑ s, t s ^ 2))⁻¹ • t

theorem unitOf_sq {t : Fin 5 → ℝ} (ht : t ≠ 0) : ∑ s, unitOf t s ^ 2 = 1 := by
  have hp := norm_sq_pos ht
  have hr : Real.sqrt (∑ s, t s ^ 2) ^ 2 = ∑ s, t s ^ 2 := Real.sq_sqrt hp.le
  simp only [unitOf, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow, hr]
  field_simp

theorem gamma_unitOf {t : Fin 5 → ℝ} (ht : t ≠ 0) :
    gamma t = (Real.sqrt (∑ s, t s ^ 2) : ℂ) • gamma (unitOf t) := by
  have hp := norm_sq_pos ht
  have hr : Real.sqrt (∑ s, t s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  rw [unitOf, gamma_smul, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hr), one_smul]

theorem one_add_gamma_eq {t : Fin 5 → ℝ} (ht : t ≠ 0) (t₀ : ℝ) :
    (t₀ : ℂ) • (1 : Matrix Four Four ℂ) + gamma t =
      ((t₀ + Real.sqrt (∑ s, t s ^ 2) : ℝ) : ℂ) • side (unitOf t) +
        ((t₀ - Real.sqrt (∑ s, t s ^ 2) : ℝ) : ℂ) • side (-unitOf t) := by
  rw [gamma_unitOf ht]
  simp only [side, γv_neg]
  change (t₀ : ℂ) • (1 : Matrix Four Four ℂ) + _ • γv (unitOf t) = _
  push_cast
  module

/-- **The cone:** `t₀ + Σ t_sγ_s ≥ 0` exactly when `t₀ ≥ |t|`. -/
theorem cone_posSemidef_iff (t₀ : ℝ) (t : Fin 5 → ℝ) :
    ((t₀ : ℂ) • (1 : Matrix Four Four ℂ) + gamma t).PosSemidef ↔
      Real.sqrt (∑ s, t s ^ 2) ≤ t₀ := by
  by_cases ht : t = 0
  · subst ht
    have hg : gamma (0 : Fin 5 → ℝ) = 0 := by simp [gamma, γv]
    simp only [hg, add_zero, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    constructor
    · intro h
      have h1 := h.dotProduct_mulVec_nonneg (Pi.single (0, 0) 1)
      simp [Matrix.smul_mulVec, dotProduct, Pi.single_apply] at h1
      exact_mod_cast h1
    · intro h
      exact Matrix.PosSemidef.one.smul (by exact_mod_cast h)
  · have hu := unitOf_sq ht
    have hu' : ∑ s, (-unitOf t) s ^ 2 = 1 := by simpa using hu
    rw [one_add_gamma_eq ht]
    constructor
    · intro h
      have htr := trace_side (-unitOf t)
      obtain ⟨j, hj⟩ : ∃ j, side (-unitOf t) *ᵥ Pi.single j 1 ≠ 0 := by
        by_contra hall
        push_neg at hall
        have : side (-unitOf t) = 0 := by
          ext a b
          have := congrFun (hall b) a
          simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
        rw [this, Matrix.trace_zero] at htr
        norm_num at htr
      set φ := side (-unitOf t) *ᵥ Pi.single j 1 with hφ
      have hφm : side (-unitOf t) *ᵥ φ = φ := by
        rw [hφ, Matrix.mulVec_mulVec, side_mul_self _ hu']
      have hφp : side (unitOf t) *ᵥ φ = 0 := by
        rw [hφ, Matrix.mulVec_mulVec]
        have := side_mul_side_neg (unitOf t) hu
        rw [this, Matrix.zero_mulVec]
      have h1 := h.dotProduct_mulVec_nonneg φ
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hφm, hφp, smul_zero,
        zero_add, dotProduct_smul] at h1
      have h2 : star φ ⬝ᵥ φ = (normSq φ : ℂ) := dot_self_eq φ
      have hpos : 0 < normSq φ := by
        rcases (normSq_nonneg φ).lt_or_eq with h3 | h3
        · exact h3
        · exfalso
          apply hj
          have h4 : star φ ⬝ᵥ φ = 0 := by rw [h2, ← h3]; simp
          exact dotProduct_star_self_eq_zero.mp h4
      rw [h2, smul_eq_mul, ← Complex.ofReal_mul] at h1
      have h5 : 0 ≤ (t₀ - Real.sqrt (∑ s, t s ^ 2)) * normSq φ := by exact_mod_cast h1
      by_contra hlt
      push_neg at hlt
      have : (t₀ - Real.sqrt (∑ s, t s ^ 2)) * normSq φ < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hpos
      linarith
    · intro h
      have hp1 : (0 : ℂ) ≤ ((t₀ + Real.sqrt (∑ s, t s ^ 2) : ℝ) : ℂ) := by
        have := Real.sqrt_nonneg (∑ s, t s ^ 2)
        exact_mod_cast (by linarith : (0 : ℝ) ≤ t₀ + Real.sqrt (∑ s, t s ^ 2))
      have hp2 : (0 : ℂ) ≤ ((t₀ - Real.sqrt (∑ s, t s ^ 2) : ℝ) : ℂ) := by
        exact_mod_cast (by linarith : (0 : ℝ) ≤ t₀ - Real.sqrt (∑ s, t s ^ 2))
      exact ((side_posSemidef _ hu).smul hp1).add ((side_posSemidef _ hu').smul hp2)

/-- **The edge of the cone:** for `t ≠ 0`, `t₀ = |t|` exactly when `X = 2t₀ Q_{t/|t|}`. -/
theorem cone_edge_iff (t₀ : ℝ) {t : Fin 5 → ℝ} (ht : t ≠ 0) :
    t₀ = Real.sqrt (∑ s, t s ^ 2) ↔
      (t₀ : ℂ) • (1 : Matrix Four Four ℂ) + gamma t = ((2 * t₀ : ℝ) : ℂ) • side (unitOf t) := by
  have hp := norm_sq_pos ht
  set r := Real.sqrt (∑ s, t s ^ 2) with hr
  have hg := gamma_unitOf ht
  rw [← hr] at hg
  have hu := unitOf_sq ht
  constructor
  · intro h
    rw [hg, side, h]
    change ((r : ℂ)) • (1 : Matrix Four Four ℂ) + (r : ℂ) • γv (unitOf t) = _
    push_cast
    module
  · intro h
    rw [hg, side] at h
    change (t₀ : ℂ) • (1 : Matrix Four Four ℂ) + (r : ℂ) • γv (unitOf t) =
      ((2 * t₀ : ℝ) : ℂ) • ((1 / 2 : ℂ) • (1 + γv (unitOf t))) at h
    have h2 : ((r - t₀ : ℝ) : ℂ) • γv (unitOf t) = 0 := by
      have e : ((r - t₀ : ℝ) : ℂ) • γv (unitOf t) = (t₀ : ℂ) • (1 : Matrix Four Four ℂ) +
          (r : ℂ) • γv (unitOf t) - ((2 * t₀ : ℝ) : ℂ) • ((1 / 2 : ℂ) • (1 + γv (unitOf t))) := by
        push_cast
        module
      rw [e, h, sub_self]
    have hγ : γv (unitOf t) ≠ 0 := by
      intro h0
      have := γv_mul_self (unitOf t)
      rw [h0, hu, Matrix.zero_mul] at this
      have h3 := congrFun (congrFun this (0, 0)) (0, 0)
      simp at h3
    have h3 := (smul_eq_zero.mp h2).resolve_right hγ
    have h4 : r - t₀ = 0 := by exact_mod_cast h3
    linarith

/-! ## Proposition 19 -/

theorem map_ofReal_mul {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    (A * B).map ((↑) : ℝ → ℂ) = A.map (↑) * B.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- **The half of every division:** for every orthogonal projector `P` (real, symmetric,
idempotent) onto the divided part, `q = 1 − P + iP` has `q² = θ`, `qᵀq = θ`, `q†q = 1`, `q⁴ = 1`,
and the square roots of the two parts make `i`. -/
theorem half_general_props {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hS : Pᵀ = P) (hP : P * P = P) :
    halfOf P * halfOf P = (1 - (2 : ℝ) • P).map (↑) ∧
    (halfOf P)ᵀ * halfOf P = (1 - (2 : ℝ) • P).map (↑) ∧
    (halfOf P)ᴴ * halfOf P = 1 ∧ halfOf P ^ 4 = 1 ∧
    halfOf P * halfOf (1 - P) = Complex.I • (1 : Matrix n n ℂ) := by
  set Pc : Matrix n n ℂ := P.map (↑) with hPc
  have hPc2 : Pc * Pc = Pc := by rw [hPc, ← map_ofReal_mul, hP]
  have hPcT : Pcᵀ = Pc := by rw [hPc, ← Matrix.transpose_map, hS]
  have hPcH : Pcᴴ = Pc := by
    ext i j
    have := congrFun (congrFun hS j) i
    simp only [Matrix.transpose_apply] at this
    simp [hPc, Matrix.conjTranspose_apply, this]
  have hθ : (1 - (2 : ℝ) • P).map ((↑) : ℝ → ℂ) = 1 - (2 : ℂ) • Pc := by
    ext i j
    simp [hPc, Matrix.one_apply]
    split_ifs <;> simp
  have hq : halfOf P = 1 - Pc + Complex.I • Pc := rfl
  have hsq : halfOf P * halfOf P = 1 - (2 : ℂ) • Pc := by
    rw [hq]; exact WholePicture.half_general Pc hPc2
  have hT : (halfOf P)ᵀ = halfOf P := by
    rw [hq, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      hPcT]
  refine ⟨by rw [hsq, hθ], by rw [hT, hsq, hθ], ?_, ?_, ?_⟩
  · rw [hq]; exact WholePicture.half_general_unitary Pc hPc2 hPcH
  · have h4 : (1 - (2 : ℂ) • Pc) * (1 - (2 : ℂ) • Pc) = 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, hPc2, smul_smul]
      module
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hsq, h4]
  · have hc : (1 - P).map ((↑) : ℝ → ℂ) = 1 - Pc := by
      ext i j
      simp [hPc, Matrix.one_apply]
      split_ifs <;> simp
    have hq' : halfOf (1 - P) = 1 - (1 - Pc) + Complex.I • (1 - Pc) := by
      rw [halfOf, hc]
    rw [hq, hq']
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hPc2, smul_smul, smul_sub, Complex.I_mul_I]
    module

/-- **The metric of every division:** `g_D(v) = p(q v) = |(1 − P)v|² − |Pv|²`. -/
theorem metricOf_eq (P : Matrix (Fin 6) (Fin 6) ℝ) (hS : Pᵀ = P) (hP : P * P = P)
    (v : Fin 6 → ℝ) :
    metricOf P v = ((∑ a, ((1 - P) *ᵥ v) a ^ 2 - ∑ a, (P *ᵥ v) a ^ 2 : ℝ) : ℂ) := by
  set x := (1 - P) *ᵥ v with hx
  set y := P *ᵥ v with hy
  have hyy : y ⬝ᵥ y = v ⬝ᵥ y := by
    rw [hy, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, Matrix.mulVec_mulVec, hP,
      dotProduct_comm]
  have hxv : x = v - y := by rw [hx, hy, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hcross : ∑ a, x a * y a = 0 := by
    have h1 : x ⬝ᵥ y = 0 := by rw [hxv, sub_dotProduct, hyy, sub_self]
    simpa [dotProduct] using h1
  have hqv : halfOf P *ᵥ (fun a => (v a : ℂ)) = fun a => (x a : ℂ) + Complex.I * (y a : ℂ) := by
    funext a
    have ex : (x a : ℂ) = ((1 - P).map ((↑) : ℝ → ℂ) *ᵥ fun a => (v a : ℂ)) a := by
      rw [hx]
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have ey : (y a : ℂ) = (P.map ((↑) : ℝ → ℂ) *ᵥ fun a => (v a : ℂ)) a := by
      rw [hy]
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have hc : (1 - P).map ((↑) : ℝ → ℂ) = 1 - P.map (↑) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp
    rw [ex, ey, hc]
    simp only [halfOf, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [metricOf, hqv, pSix]
  have e2 : ∀ a, ((x a : ℂ) + Complex.I * (y a : ℂ)) ^ 2 =
      ((x a ^ 2 - y a ^ 2 : ℝ) : ℂ) + 2 * Complex.I * ((x a * y a : ℝ) : ℂ) := by
    intro a
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, hcross, Finset.sum_sub_distrib]
  simp

/-- `θ = 1 − 2P` with complex entries. -/
theorem theta_map_eq {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) :
    (1 - (2 : ℝ) • P).map ((↑) : ℝ → ℂ) = 1 - (2 : ℂ) • P.map (↑) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

/-- **The half is made from the sign:** `q = (1+i)/2 + ((1−i)/2)θ`. -/
theorem halfOf_eq_combo {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) :
    halfOf P = ((1 + Complex.I) / 2) • (1 : Matrix n n ℂ) +
      ((1 - Complex.I) / 2) • (1 - (2 : ℝ) • P).map (↑) := by
  rw [theta_map_eq, halfOf]
  module

/-- **The conjugate half:** `q̄ = (1 − P) − iP = (1−i)/2 + ((1+i)/2)θ`. -/
theorem halfOf_map_star {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) :
    (halfOf P).map star = ((1 - Complex.I) / 2) • (1 : Matrix n n ℂ) +
      ((1 + Complex.I) / 2) • (1 - (2 : ℝ) • P).map (↑) := by
  have h : (halfOf P).map star = 1 - P.map (↑) - Complex.I • P.map (↑) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [halfOf, Matrix.one_apply, Complex.ext_iff]
    · simp [halfOf, Matrix.one_apply, hij, Complex.ext_iff]
  rw [h, theta_map_eq]
  module

/-- **The square roots of every division but the point:** with `θ = 1 − 2P`, `P ≠ 0`, `P ≠ 1`,
`(α + βθ)² = θ` exactly when `α² + β² = 0` and `2αβ = 1`. -/
theorem halves_iff_general {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P * P = P) (h0 : P ≠ 0) (h1 : P ≠ 1) (α β : ℂ) :
    (α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℝ) • P).map (↑)) ^ 2 = (1 - (2 : ℝ) • P).map (↑) ↔
      α ^ 2 + β ^ 2 = 0 ∧ 2 * α * β = 1 := by
  rw [theta_map_eq]
  set Pc : Matrix n n ℂ := P.map (↑) with hPc
  have hPc2 : Pc * Pc = Pc := by rw [hPc, ← map_ofReal_mul, hP]
  have hsq : (α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℂ) • Pc)) ^ 2 =
      ((α + β) ^ 2) • (1 : Matrix n n ℂ) + ((α - β) ^ 2 - (α + β) ^ 2) • Pc := by
    rw [sq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPc2, smul_smul, smul_sub]
    module
  rw [hsq]
  obtain ⟨x, hx, hPx⟩ : ∃ x : n → ℂ, x ≠ 0 ∧ Pc *ᵥ x = x := by
    obtain ⟨j, hj⟩ : ∃ j, Pc *ᵥ Pi.single j 1 ≠ 0 := by
      by_contra h
      push_neg at h
      have hPc0 : Pc = 0 := by
        ext i j
        have := congrFun (h j) i
        simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
      apply h0
      apply Matrix.map_injective Complex.ofReal_injective
      show P.map ((↑) : ℝ → ℂ) = (0 : Matrix n n ℝ).map ((↑) : ℝ → ℂ)
      rw [Matrix.map_zero _ Complex.ofReal_zero]
      exact hPc0
    exact ⟨_, hj, by rw [Matrix.mulVec_mulVec, hPc2]⟩
  obtain ⟨y, hy, hPy⟩ : ∃ y : n → ℂ, y ≠ 0 ∧ Pc *ᵥ y = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, (1 - Pc) *ᵥ Pi.single j 1 ≠ 0 := by
      by_contra h
      push_neg at h
      have h' : (1 : Matrix n n ℂ) - Pc = 0 := by
        ext i j
        have := congrFun (h j) i
        simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
      apply h1
      apply Matrix.map_injective Complex.ofReal_injective
      show P.map ((↑) : ℝ → ℂ) = (1 : Matrix n n ℝ).map ((↑) : ℝ → ℂ)
      rw [Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
      exact (sub_eq_zero.mp h').symm
    refine ⟨_, hj, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hPc2, sub_self, Matrix.zero_mulVec]
  have evx : ∀ a b : ℂ, (a • (1 : Matrix n n ℂ) + b • Pc) *ᵥ x = (a + b) • x := by
    intro a b
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hPx,
      add_smul]
  have evy : ∀ a b : ℂ, (a • (1 : Matrix n n ℂ) + b • Pc) *ᵥ y = a • y := by
    intro a b
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hPy,
      smul_zero, add_zero]
  have hθ : (1 : Matrix n n ℂ) - (2 : ℂ) • Pc = (1 : ℂ) • (1 : Matrix n n ℂ) + (-2 : ℂ) • Pc := by
    rw [one_smul, neg_smul, sub_eq_add_neg]
  rw [hθ]
  constructor
  · intro h
    have hx' := congrArg (fun M => M *ᵥ x) h
    have hy' := congrArg (fun M => M *ᵥ y) h
    simp only [evx, evy] at hx' hy'
    have c1 : (α + β) ^ 2 + ((α - β) ^ 2 - (α + β) ^ 2) - (1 + -2) = 0 := by
      have := sub_eq_zero.mpr hx'
      rw [← sub_smul] at this
      exact (smul_eq_zero.mp this).resolve_right hx
    have c2 : (α + β) ^ 2 - 1 = 0 := by
      have := sub_eq_zero.mpr hy'
      rw [← sub_smul] at this
      exact (smul_eq_zero.mp this).resolve_right hy
    constructor
    · linear_combination c1 / 2 + c2 / 2
    · linear_combination c2 / 2 - c1 / 2
  · rintro ⟨e1, e2⟩
    have ha : (α + β) ^ 2 = 1 := by linear_combination e1 + e2
    have hb : (α - β) ^ 2 - (α + β) ^ 2 = -2 := by linear_combination -2 * e2
    rw [hb, ha]

/-- **The four square roots:** for every division but the point, `(α + βθ)² = θ` exactly when `α + βθ`
is one of `±q`, `±q̄`. -/
theorem halves_general {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P * P = P) (h0 : P ≠ 0) (h1 : P ≠ 1) (α β : ℂ) :
    ((α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℝ) • P).map (↑)) ^ 2 = (1 - (2 : ℝ) • P).map (↑) ↔
      α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℝ) • P).map (↑) ∈
        ({halfOf P, -halfOf P, (halfOf P).map star, -(halfOf P).map star} :
          Set (Matrix n n ℂ))) := by
  have hq := halfOf_eq_combo P
  have hqb := halfOf_map_star P
  have key : ∀ a b : ℂ, ((a = (1 + Complex.I) / 2 ∧ b = (1 - Complex.I) / 2) ∨
      (a = -((1 + Complex.I) / 2) ∧ b = -((1 - Complex.I) / 2)) ∨
      (a = (1 - Complex.I) / 2 ∧ b = (1 + Complex.I) / 2) ∨
      (a = -((1 - Complex.I) / 2) ∧ b = -((1 + Complex.I) / 2))) →
      (a • (1 : Matrix n n ℂ) + b • (1 - (2 : ℝ) • P).map (↑)) ^ 2 = (1 - (2 : ℝ) • P).map (↑) :=
    fun a b hab => (halves_iff_general P hP h0 h1 a b).mpr ((halves_solutions a b).mpr hab)
  constructor
  · intro h
    rcases (halves_solutions α β).mp ((halves_iff_general P hP h0 h1 α β).mp h) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hq.symm
    · refine Or.inr (Or.inl ?_)
      rw [hq, neg_add, ← neg_smul, ← neg_smul]
    · exact Or.inr (Or.inr (Or.inl hqb.symm))
    · refine Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mpr ?_)))
      rw [hqb, neg_add, ← neg_smul, ← neg_smul]
  · intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · rw [h, hq]; exact key _ _ (Or.inl ⟨rfl, rfl⟩)
    · rw [h, hq, neg_add, ← neg_smul, ← neg_smul]
      exact key _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rw [h, hqb]; exact key _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · rw [h, hqb, neg_add, ← neg_smul, ← neg_smul]
      exact key _ _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- **No real half:** for every division but the point no real `α, β` have `(α + βθ)² = θ`. -/
theorem no_real_half_general {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P * P = P) (h0 : P ≠ 0) (h1 : P ≠ 1) (α β : ℝ) :
    ((α : ℂ) • (1 : Matrix n n ℂ) + (β : ℂ) • (1 - (2 : ℝ) • P).map (↑)) ^ 2 ≠
      (1 - (2 : ℝ) • P).map (↑) := by
  intro h
  obtain ⟨e1, e2⟩ := (halves_iff_general P hP h0 h1 _ _).mp h
  exact no_real_half α β ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

/-- In the basis `f_a` a division is a set `D`, its projector the diagonal of `D`, and its half is
the coordinate half `half D`. -/
theorem halfOf_diag (D : Finset (Fin 6)) :
    halfOf (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) = half D := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ D <;> simp [halfOf, half, Matrix.one_apply, hi]
  · simp [halfOf, half, Matrix.one_apply, Matrix.diagonal_apply, hij]

/-- **The half on the sixty-four sets:** `q_D f_S = i^{|S ∩ D|} f_S`. -/
theorem half_fS (D S : Finset (Fin 6)) :
    ExteriorAlgebra.map (Matrix.toLin' (half D)) (fS S) = Complex.I ^ (S ∩ D).card • fS S := by
  have hq : ∀ a, Matrix.toLin' (half D) (fvec a) = (if a ∈ D then Complex.I else 1) • fvec a := by
    intro a
    ext b
    simp [half, fvec, Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.single_apply]
    split_ifs <;> simp_all
  rw [fS, ExteriorAlgebra.map_apply_ιMulti]
  have hcomp : (Matrix.toLin' (half D) ∘ fun k => fvec (S.orderEmbOfFin rfl k)) =
      fun k => (if S.orderEmbOfFin rfl k ∈ D then Complex.I else 1) •
        fvec (S.orderEmbOfFin rfl k) := by
    funext k
    exact hq _
  rw [hcomp, AlternatingMap.map_smul_univ]
  congr 1
  rw [← half_on_sets D S]
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl, Finset.prod_map]
  rfl

/-- `Σ_a [a = b] • rel (six a) = rel (six b)`. -/
theorem sum_single_six (b : Fin 6) :
    ∑ a, (Pi.single b (1 : ℂ) : Fin 6 → ℂ) a • rel (Article.six a) = rel (Article.six b) := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Pi.single_apply, hab]
  · simp

/-- The half of P3's division on the six: `1` on the singlet, `i` on the five directions. -/
def qSix (t : Fin 6 → ℂ) : Fin 6 → ℂ := fun a => if a = 0 then t a else Complex.I * t a

/-- **P3's real six is the square root of the sign of P1's:** `P3's real six = q(P1's real six)`. -/
theorem P3six_eq_half_P1six :
    P3six = (fun t => ∑ a, qSix t a • rel (Article.six a)) ''
      {t | (∑ a, t a • rel (Article.six a)) ∈ P1six} := by
  ext v
  constructor
  · intro hv
    obtain ⟨t', rfl⟩ := (mem_sixDirections_iff v).mp hv.1
    have hr := (mem_P3six_iff t').mp hv
    refine ⟨fun a => if a = 0 then t' a else -Complex.I * t' a, ?_, ?_⟩
    · show _ ∈ P1six
      rw [mem_P1six_iff]
      refine ⟨by simpa using hr 0, fun s => ?_⟩
      simp [Fin.succ_ne_zero, Complex.mul_re, hr s.succ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a = 0
      · simp [qSix, ha]
      · simp only [qSix, ha, if_false]
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_setOf_eq, mem_P1six_iff] at ht
    rw [mem_P3six_iff]
    intro a
    by_cases ha : a = 0
    · subst ha; simp [qSix, ht.1]
    · obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.mpr ha
      simp [qSix, Fin.succ_ne_zero, Complex.mul_im, ht.2 s]

theorem gen_inl_eq (s : Fin 5) : gen (Sum.inl s) = Complex.I • γ s := by
  show Complex.I • obs (lineIdx s) = _
  rw [obs_lineIdx]

end Geometry

open Comparison.System.Geometry

/-- **Proposition 16 (the six directions).** The singlet and the five vector states `Ω, ℓ₁, …, ℓ₅`
(`ℓ_s = (γ_s ⊗ 1)Ω`) are orthonormal and are the six directions (the antisymmetric two-spinor states); for
`v = t₀Ω + Σ t_sℓ_s`: `p(v) = t₀² − Σ t_s²` and `‖v‖² = |t₀|² + Σ|t_s|²`; P1's real six
(`p(v) = ‖v‖²`) are the `v` with `t₀` real and every `t_s` imaginary; P3's real six
(`(Θ ⊗ Θ)v = v`) are the `v` with every `t` real. Recognition: none. -/
theorem prop_16 :
    (∀ a b : Fin 6, star (rel (Article.six a)) ⬝ᵥ rel (Article.six b) = if a = b then 1 else 0) ∧
    rel (Article.six 0) = Ω ∧
    (∀ s : Fin 5, rel (Article.six s.succ) = (γ s ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) ∧
    (∀ v : Two → ℂ, v ∈ sixDirections ↔ ∃ t : Fin 6 → ℂ, v = ∑ a, t a • rel (Article.six a)) ∧
    (∀ t : Fin 6 → ℂ, pfRel (∑ a, t a • rel (Article.six a)) = t 0 ^ 2 - ∑ s : Fin 5, t s.succ ^ 2) ∧
    (∀ t : Fin 6 → ℂ, star (∑ a, t a • rel (Article.six a)) ⬝ᵥ (∑ a, t a • rel (Article.six a)) =
      ∑ a, ((Complex.normSq (t a) : ℝ) : ℂ)) ∧
    (∀ t : Fin 6 → ℂ, (∑ a, t a • rel (Article.six a)) ∈ P1six ↔
      (t 0).im = 0 ∧ ∀ s : Fin 5, (t s.succ).re = 0) ∧
    (∀ t : Fin 6 → ℂ, (∑ a, t a • rel (Article.six a)) ∈ P3six ↔ ∀ a, (t a).im = 0) := by
  refine ⟨fun a b => ?_, rel_six_zero, rel_six_succ, mem_sixDirections_iff, pfRel_six,
    Article.norm_six, mem_P1six_iff, mem_P3six_iff⟩
  rw [rel_inner]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h (Article.six_injective h'))]

/-- **Proposition 17 (the fifteen rotations and the ten).** `su(4) = sp(2) ⊕ iQ` (the fifteen generators:
the ten of `sp(2)` and the five `iγ_s`); `U ↦ U ⊗ U` acts on P1's real six as a rotation
(`(U ⊗ U)ι(t) = ι(R_U t)`), of determinant one, every rotation of `SO(6)` is some `R_U`, and `R_U = 1`
exactly when `U = ±1`; the singlet goes to every point of the five-sphere;
`e^{iaγ_s} = cos a + i sin a γ_s` and `(e^{iaγ_s} ⊗ e^{iaγ_s})Ω = cos 2a Ω + sin 2a iℓ_s`; the rotations
keeping `Ω` are `Sp(2)`, those keeping `L` are `Sp(2) ∪ i Sp(2)`; P3's own division (the five directions
against the singlet) keeps the ten and moves the five. Recognition: none. -/
theorem prop_17 :
    (su4 = sp2 ⊔ Submodule.span ℝ (Set.range fun s : Fin 5 => gen (Sum.inl s)) ∧
      Disjoint sp2 (Submodule.span ℝ (Set.range fun s : Fin 5 => gen (Sum.inl s)))) ∧
    (∀ s : Fin 5, gen (Sum.inl s) = Complex.I • γ s) ∧
    finrank ℝ su4 = 15 ∧ finrank ℝ sp2 = 10 ∧
    (∀ (U : GroupsContinuumLaw.SU4) (t : GroupsContinuumLaw.E6),
      ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) *ᵥ relOf (GroupsContinuumLaw.ι6 t) =
        relOf (GroupsContinuumLaw.ι6 (GroupsContinuumLaw.rot6Hom U t))) ∧
    (∀ U : GroupsContinuumLaw.SU4, LinearMap.det (GroupsContinuumLaw.rot6Hom U).toLinearMap = 1) ∧
    (∀ φ : GroupsContinuumLaw.E6 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E6, LinearMap.det φ.toLinearMap = 1 →
      ∃ U : GroupsContinuumLaw.SU4, GroupsContinuumLaw.rot6Hom U = φ) ∧
    (∀ U : GroupsContinuumLaw.SU4, GroupsContinuumLaw.rot6Hom U = 1 ↔
      (U : Matrix Four Four ℂ) = 1 ∨ (U : Matrix Four Four ℂ) = -1) ∧
    (∀ n : GroupsContinuumLaw.E6, ∑ a, n a ^ 2 = 1 →
      ∃ U : GroupsContinuumLaw.SU4, GroupsContinuumLaw.rot6Hom U GroupsContinuumLaw.e0 = n) ∧
    (∀ (a : ℝ) (s : Fin 5),
      NormedSpace.exp ((a : ℂ) • (Complex.I • γ s)) =
        (Real.cos a : ℂ) • (1 : Matrix Four Four ℂ) + (Real.sin a : ℂ) • (Complex.I • γ s) ∧
      (NormedSpace.exp ((a : ℂ) • (Complex.I • γ s)) ⊗ₖ
          NormedSpace.exp ((a : ℂ) • (Complex.I • γ s))) *ᵥ Ω =
        (Real.cos (2 * a) : ℂ) • Ω + (Real.sin (2 * a) : ℂ) • (Complex.I • ((γ s ⊗ₖ 1) *ᵥ Ω))) ∧
    (∀ U : Matrix Four Four ℂ, (U ⊗ₖ U) *ᵥ Ω = Ω ↔ U * J * Uᵀ = J) ∧
    (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U.det = 1 →
      ((U ⊗ₖ U) * L = L * (U ⊗ₖ U) ↔
        U * J * Uᵀ = J ∨ (Complex.I • U) * J * (Complex.I • U)ᵀ = J)) ∧
    (∀ x : Fin 5 ⊕ Fin 10, Kept {1, 2, 3, 4, 5} x ↔ x.isRight) := by
  refine ⟨su4_eq_sup, gen_inl_eq, finrank_su4, finrank_sp2, GroupsContinuumLaw.kron_six, GroupsContinuumLaw.rot6_det,
    GroupsContinuumLaw.rot6_onto, GroupsContinuumLaw.rot6_ker, fun n hn => ?_, exp_line_on_singlet, keeps_singlet_iff,
    fun U hU hdet => ?_, P3_division_keeps_ten⟩
  · obtain ⟨c, s, m, hcs, hm, -, h⟩ := GroupsContinuumLaw.exists_boost n hn
    exact ⟨_, h⟩
  · rw [keeps_L_iff U hU hdet, neg_iff_I_smul]

/-- **Proposition 18 (the sign of time).** For `X = t₀ + Σ t_sγ_s`: `det X = (t₀² − Σ t_s²)²`;
for real `t`, `X ≥ 0` exactly when `t₀ ≥ |t|`, and for `t ≠ 0`, `t₀ = |t|` exactly when
`X = 2t₀Q_{t/|t|}`; on P3's real six `p = t₀² − |t|²`, with `p(Ω) = 1` and `p(ℓ_s) = −1` in the
orthonormal basis `Ω, ℓ_s`: signature `(1, 5)`; and P3's real six is `q(P1's real six)`, `q = 1` on `Ω`
and `i` on the five directions. Recognition: the singlet is time-like and the five directions space-like; the singlet
is the time of a pair and the five directions its space. -/
theorem prop_18 :
    (∀ (t₀ : ℂ) (t : Fin 5 → ℂ),
      (t₀ • (1 : Matrix Four Four ℂ) + ∑ s, t s • γ s).det = (t₀ ^ 2 - ∑ s, t s ^ 2) ^ 2) ∧
    (∀ (t₀ : ℝ) (t : Fin 5 → ℝ), ((t₀ : ℂ) • (1 : Matrix Four Four ℂ) + gamma t).PosSemidef ↔
      Real.sqrt (∑ s, t s ^ 2) ≤ t₀) ∧
    (∀ (t₀ : ℝ) (t : Fin 5 → ℝ), t ≠ 0 → (t₀ = Real.sqrt (∑ s, t s ^ 2) ↔
      (t₀ : ℂ) • (1 : Matrix Four Four ℂ) + gamma t = ((2 * t₀ : ℝ) : ℂ) • side (unitOf t))) ∧
    (∀ t : Fin 6 → ℝ, pfRel (∑ a, (t a : ℂ) • rel (Article.six a)) =
      ((t 0 ^ 2 - ∑ s : Fin 5, t s.succ ^ 2 : ℝ) : ℂ)) ∧
    pfRel (rel (Article.six 0)) = 1 ∧ (∀ s : Fin 5, pfRel (rel (Article.six s.succ)) = -1) ∧
    P3six = (fun t => ∑ a, qSix t a • rel (Article.six a)) ''
      {t | (∑ a, t a • rel (Article.six a)) ∈ P1six} := by
  refine ⟨det_cone, cone_posSemidef_iff, fun t₀ t ht => cone_edge_iff t₀ ht, fun t => ?_, ?_,
    fun s => ?_, P3six_eq_half_P1six⟩
  · rw [pfRel_six]
    push_cast
    rfl
  · rw [← sum_single_six 0, pfRel_six]
    simp [Fin.succ_ne_zero]
  · rw [← sum_single_six s.succ, pfRel_six]
    simp [Fin.succ_ne_zero, Pi.single_apply]

/-- **Proposition 19 (the square root of the sign).** For every division, given by the orthogonal projector `P` onto its
divided part, the square root of the sign `q = 1 − P + iP` has `q² = qᵀq = θ = 1 − 2P`, `q†q = 1`, `q⁴ = 1` and
`q_Dq_{D′} = i`; for every Hermitian projector `P` (complex) the same `q = 1 − P + iP` has `q² = 1 − 2P`
and `q†q = 1`; for every division but the point, `(α + βθ)² = θ` exactly when `α + βθ` is `±q` or
`±q̄`, and no real `α, β` do it; the metric is `g_D(v) = p(qv) = |v_{D′}|² − |v_D|²`; in the basis
`f_a` the square root of the sign of the set `D` is the coordinate half, `q_Df_S = i^{|S∩D|}f_S`, and `i^{|S|}` is
`1, i, −1, −i` on `16, 12, 16, 20` of the sixty-four sets. Recognition: the `i` of quantum theory and
the metric of gravity are the square root of the sign and its square. -/
theorem prop_19 :
    (∀ {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ), Pᵀ = P → P * P = P →
      halfOf P * halfOf P = (1 - (2 : ℝ) • P).map (↑) ∧
      (halfOf P)ᵀ * halfOf P = (1 - (2 : ℝ) • P).map (↑) ∧
      (halfOf P)ᴴ * halfOf P = 1 ∧ halfOf P ^ 4 = 1 ∧
      halfOf P * halfOf (1 - P) = Complex.I • (1 : Matrix n n ℂ)) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ), P * P = P →
      (1 - P + Complex.I • P) * (1 - P + Complex.I • P) = 1 - (2 : ℂ) • P ∧
      (Pᴴ = P → (1 - P + Complex.I • P)ᴴ * (1 - P + Complex.I • P) = 1)) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ), P * P = P → P ≠ 0 → P ≠ 1 →
      ∀ α β : ℂ, ((α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℝ) • P).map (↑)) ^ 2 =
          (1 - (2 : ℝ) • P).map (↑) ↔
        α • (1 : Matrix n n ℂ) + β • (1 - (2 : ℝ) • P).map (↑) ∈
          ({halfOf P, -halfOf P, (halfOf P).map star, -(halfOf P).map star} :
            Set (Matrix n n ℂ)))) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ), P * P = P → P ≠ 0 → P ≠ 1 →
      ∀ α β : ℝ, ((α : ℂ) • (1 : Matrix n n ℂ) + (β : ℂ) • (1 - (2 : ℝ) • P).map (↑)) ^ 2 ≠
        (1 - (2 : ℝ) • P).map (↑)) ∧
    (∀ P : Matrix (Fin 6) (Fin 6) ℝ, Pᵀ = P → P * P = P → ∀ v : Fin 6 → ℝ,
      metricOf P v = ((∑ a, ((1 - P) *ᵥ v) a ^ 2 - ∑ a, (P *ᵥ v) a ^ 2 : ℝ) : ℂ)) ∧
    (∀ D : Finset (Fin 6), halfOf (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) = half D) ∧
    (∀ D S : Finset (Fin 6),
      ExteriorAlgebra.map (Matrix.toLin' (half D)) (fS S) = Complex.I ^ (S ∩ D).card • fS S) ∧
    ((Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 0).card = 16 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 1).card = 12 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 2).card = 16 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 3).card = 20) :=
  ⟨fun P hS hP => half_general_props P hS hP,
    fun P hP => ⟨WholePicture.half_general P hP, fun hH => WholePicture.half_general_unitary P hP hH⟩,
    fun P hP h0 h1 => halves_general P hP h0 h1,
    fun P hP h0 h1 => no_real_half_general P hP h0 h1, metricOf_eq, halfOf_diag, half_fS,
    sets_count⟩

end Comparison.System
