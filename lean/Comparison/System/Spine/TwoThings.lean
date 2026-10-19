import Comparison.System.Postulates

/-!
# The spine: the two systems of every candidate system are the model's two systems

P1 gives two systems the space `H ⊗ H` with the inner product of
the
tensor product. A gauge `f` of a candidate system `S` gives the product basis of `H ⊗ H`, and its
coordinates `f.c2 : H ⊗ H → ℂ¹⁶` carry

* the exchange of the two systems (`TensorProduct.comm`) to the model's swap `P` (`c2_comm`);
* every operator `X ⊗ Y` to the Kronecker product of the matrices of `X` and `Y` (`c2_map`);
* the singlet `Ω_S = ½ Σ_j u_j ⊗ Θu_j` of the gauge's basis to the model's `Ω` (`c2_singlet`);
* the comparison `L_S = 1 ⊗ 1 + Σ_s γ_s ⊗ γ_s` of the gauge's five lines to the model's `L`
  (`c2_comparison`).

Two gauges differ by one rotation `U ∈ Sp(2)` (`frames_differ`), which keeps `L` (`comparison_P2`), so
the
comparison does not depend on the gauge (`comparisonOf_eq`): every candidate system has one
comparison, `S.comparison`, carried by every gauge to `L`. So every statement about the model's two
systems holds for the two systems of every candidate system.
-/

namespace Comparison.System

open Matrix Complex
open scoped TensorProduct InnerProductSpace Kronecker

namespace CandidateSystem

namespace Frame

variable {S : CandidateSystem} (f : S.Frame)

/-- The coordinates of two systems in a gauge: the unitary map `H ⊗ H ≅ ℂ¹⁶` of the product basis.
-/
noncomputable def e2 : P1.TwoThings S.H ≃ₗᵢ[ℂ] EuclideanSpace ℂ Two :=
  (f.b.tensorProduct f.b).repr

/-- The coordinates of a two-spinor state of two systems, a vector of the model's sixteen amplitudes. -/
noncomputable def c2 (z : P1.TwoThings S.H) : Two → ℂ := WithLp.ofLp (f.e2 z)

theorem c2_add (z w : P1.TwoThings S.H) : f.c2 (z + w) = f.c2 z + f.c2 w := by
  simp [c2]

theorem c2_smul (c : ℂ) (z : P1.TwoThings S.H) : f.c2 (c • z) = c • f.c2 z := by
  simp [c2]

theorem c2_zero : f.c2 0 = 0 := by
  simp [c2]

theorem c2_injective : Function.Injective f.c2 := by
  intro z w h
  apply f.e2.injective
  exact WithLp.ofLp_injective 2 h

theorem c2_sum {ι : Type*} (s : Finset ι) (z : ι → P1.TwoThings S.H) :
    f.c2 (∑ i ∈ s, z i) = ∑ i ∈ s, f.c2 (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [c2_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, c2_add, ih]

/-- **The coordinates of a product two-spinor state are the products of the coordinates.** -/
theorem c2_tmul (v w : S.H) :
    f.c2 (v ⊗ₜ w) = prodRel (WithLp.ofLp (f.e v)) (WithLp.ofLp (f.e w)) := by
  funext p
  change (f.b.tensorProduct f.b).repr (v ⊗ₜ w) p = _
  rw [OrthonormalBasis.tensorProduct_repr_tmul_apply', prodRel]
  change f.b.repr w p.2 * f.b.repr v p.1 = f.b.repr v p.1 * f.b.repr w p.2
  ring

theorem swap_mulVec_apply (g : Two → ℂ) (p : Two) : (swap *ᵥ g) p = g (p.2, p.1) := by
  have h : g = relOf (Matrix.of fun x y => g (x, y)) := by
    funext q
    rfl
  rw [h, swap_relOf]
  rfl

/-- **The exchange of the two systems is the model's swap.** -/
theorem c2_comm (z : P1.TwoThings S.H) :
    f.c2 (TensorProduct.comm ℂ S.H S.H z) = swap *ᵥ f.c2 z := by
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    funext p
    rw [TensorProduct.comm_tmul, c2_tmul, c2_tmul, swap_mulVec_apply]
    simp only [prodRel]
    ring
  | add x y hx hy => rw [map_add, c2_add, c2_add, hx, hy, Matrix.mulVec_add]

theorem ofLp_e (v : S.H) : WithLp.ofLp (f.e v) = fun q => ⟪f.b q, v⟫_ℂ := by
  funext q
  exact f.e_apply v q

theorem e_apply_op (X : S.H →ₗ[ℂ] S.H) (v : S.H) :
    WithLp.ofLp (f.e (X v)) = f.conj X *ᵥ WithLp.ofLp (f.e v) := by
  rw [f.ofLp_e, f.ofLp_e]
  funext p
  exact Partner.coord_apply f.b X v p

/-- **An operator `X ⊗ Y` on two systems is the Kronecker product of the matrices of `X` and `Y`.**
-/
theorem c2_map (X Y : S.H →ₗ[ℂ] S.H) (z : P1.TwoThings S.H) :
    f.c2 (TensorProduct.map X Y z) = (f.conj X ⊗ₖ f.conj Y) *ᵥ f.c2 z := by
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    rw [TensorProduct.map_tmul, c2_tmul, c2_tmul, e_apply_op, e_apply_op, kron_mulVec_prodRel]
  | add x y hx hy => rw [map_add, c2_add, c2_add, hx, hy, Matrix.mulVec_add]

/-- **The singlet of a gauge:** `Ω_S = ½ Σ_j u_j ⊗ Θu_j` over the gauge's basis. -/
noncomputable def singletOf : P1.TwoThings S.H :=
  (1 / 2 : ℂ) • ∑ p : Four, f.b p ⊗ₜ S.partner.Θ (f.b p)

/-- **The singlet of every gauge is the model's singlet `Ω`.** -/
theorem c2_singlet : f.c2 f.singletOf = Ω := by
  rw [singletOf, c2_smul, c2_sum]
  funext q
  have hb : ∀ p : Four, WithLp.ofLp (f.e (f.b p)) = Pi.single p 1 := by
    intro p
    change WithLp.ofLp (f.b.repr (f.b p)) = _
    rw [OrthonormalBasis.repr_self]
    rfl
  have hΘ : ∀ p : Four, WithLp.ofLp (f.e (S.partner.Θ (f.b p))) = J *ᵥ star (Pi.single p 1) := by
    intro p
    rw [f.e_partner, ofLp_modelΘ, hb]
    rfl
  simp only [c2_tmul, hb, hΘ, Pi.smul_apply, Finset.sum_apply, prodRel, smul_eq_mul]
  have hJ : J q.2 q.1 = -J q.1 q.2 := by
    have := congrFun (congrFun J_transpose q.1) q.2
    simpa using this
  rw [Finset.sum_eq_single q.1]
  · simp only [Pi.single_eq_same, one_mul, Ω, relOf, MΩ, Matrix.smul_apply, smul_eq_mul]
    have hcol : (J *ᵥ star (Pi.single q.1 (1 : ℂ))) q.2 = J q.2 q.1 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol, hJ]
    ring
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- **The comparison of a gauge:** `L_S = 1 ⊗ 1 + Σ_s γ_s ⊗ γ_s` with the gauge's five lines. -/
noncomputable def comparisonOf : Module.End ℂ (P1.TwoThings S.H) :=
  TensorProduct.map 1 1 + ∑ s, TensorProduct.map (f.lines s) (f.lines s)

/-- **The comparison of every gauge is the model's comparison `L`.** -/
theorem c2_comparison (z : P1.TwoThings S.H) : f.c2 (f.comparisonOf z) = L *ᵥ f.c2 z := by
  rw [comparisonOf, LinearMap.add_apply, LinearMap.sum_apply, c2_add, c2_sum, c2_map]
  simp only [c2_map, conj_lines, map_one]
  rw [L, Matrix.add_mulVec, Matrix.sum_mulVec]

/-- In two gauges the coordinates differ by the Kronecker square of the rotation between them. -/
theorem c2_change (f' : S.Frame) (U : Matrix.unitaryGroup Four ℂ)
    (hU : ∀ w : ModelH, f'.e (f.e.symm w) =
      WithLp.toLp 2 ((U : Matrix Four Four ℂ) *ᵥ WithLp.ofLp w)) (z : P1.TwoThings S.H) :
    f'.c2 z = ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) *ᵥ f.c2 z := by
  have he : ∀ v : S.H, WithLp.ofLp (f'.e v) = (U : Matrix Four Four ℂ) *ᵥ WithLp.ofLp (f.e v) := by
    intro v
    have h := hU (f.e v)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    rw [h]
  induction z using TensorProduct.inductionOn with
  | tmul v w => rw [c2_tmul, c2_tmul, he, he, kron_mulVec_prodRel]
  | add x y hx hy => rw [c2_add, c2_add, hx, hy, Matrix.mulVec_add]

end Frame

/-- **The comparison does not depend on the gauge.** -/
theorem comparisonOf_eq {S : CandidateSystem} (f f' : S.Frame) :
    f.comparisonOf = f'.comparisonOf := by
  obtain ⟨U, hU, hUe⟩ := frames_differ f f'
  have hL : ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) * L =
      L * ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) := comparison_P2.1.1 U hU
  refine LinearMap.ext fun z => ?_
  apply f'.c2_injective
  rw [Frame.c2_comparison, Frame.c2_change f f' U hUe, Frame.c2_change f f' U hUe,
    Frame.c2_comparison, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL]

/-- **The comparison of a candidate system**, `L_S`, through any of its gauges. -/
noncomputable def comparison (S : CandidateSystem) : Module.End ℂ (P1.TwoThings S.H) :=
  (Classical.choice (exists_frame S)).comparisonOf

theorem comparison_eq {S : CandidateSystem} (f : S.Frame) : S.comparison = f.comparisonOf :=
  comparisonOf_eq _ f

/-- **Every gauge carries the comparison of `S` to the model's `L`.** -/
theorem c2_comparison' {S : CandidateSystem} (f : S.Frame) (z : P1.TwoThings S.H) :
    f.c2 (S.comparison z) = L *ᵥ f.c2 z := by
  rw [comparison_eq f, Frame.c2_comparison]

/-- **The values of the comparison of every candidate system:** `6` on the singlet, `2`, `−2` on the
two-spinor states made by a plane, a line, as in the model. -/
theorem comparison_singlet {S : CandidateSystem} (f : S.Frame) :
    S.comparison f.singletOf = (6 : ℂ) • f.singletOf := by
  apply f.c2_injective
  rw [c2_comparison', Frame.c2_smul, Frame.c2_singlet, ← rel_zero, L_rel]
  simp [disagreeSet]

/-- The coordinates of two systems in a gauge, as a linear equivalence onto `Two → ℂ`. -/
noncomputable def Frame.c2L {S : CandidateSystem} (f : S.Frame) :
    P1.TwoThings S.H ≃ₗ[ℂ] (Two → ℂ) :=
  f.e2.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (Two → ℂ))

theorem Frame.c2L_apply {S : CandidateSystem} (f : S.Frame) (z : P1.TwoThings S.H) :
    f.c2L z = f.c2 z := rfl

/-- **Every gauge carries the eigenspaces of the comparison of `S` onto those of `L`.** -/
theorem eigenspace_comparison {S : CandidateSystem} (f : S.Frame) (μ : ℂ) :
    (Module.End.eigenspace S.comparison μ).map (f.c2L : P1.TwoThings S.H →ₗ[ℂ] (Two → ℂ)) =
      Module.End.eigenspace (Matrix.toLin' L) μ := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, LinearEquiv.coe_coe, Frame.c2L_apply,
      ← c2_comparison' f v, hv, Frame.c2_smul]
  · intro hw
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw
    refine ⟨f.c2L.symm w, ?_, by simp⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    apply f.c2_injective
    rw [c2_comparison', Frame.c2_smul, ← Frame.c2L_apply, LinearEquiv.apply_symm_apply, hw]

theorem finrank_eigenspace_comparison {S : CandidateSystem} (f : S.Frame) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace S.comparison μ) =
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) μ) := by
  rw [← eigenspace_comparison f μ, LinearEquiv.finrank_map_eq]

/-- **The comparison of every candidate system has the spectrum `6¹ ⊕ 2¹⁰ ⊕ (−2)⁵`.** -/
theorem comparison_spectrum (S : CandidateSystem) :
    Module.finrank ℂ (Module.End.eigenspace S.comparison 6) = 1 ∧
    Module.finrank ℂ (Module.End.eigenspace S.comparison 2) = 10 ∧
    Module.finrank ℂ (Module.End.eigenspace S.comparison (-2)) = 5 ∧
    ∀ μ : ℂ, μ ≠ 6 → μ ≠ 2 → μ ≠ -2 → Module.End.eigenspace S.comparison μ = ⊥ := by
  obtain ⟨f⟩ := exists_frame S
  refine ⟨by rw [finrank_eigenspace_comparison f, finrank_eigenspace_L_six],
    by rw [finrank_eigenspace_comparison f, finrank_eigenspace_L_two],
    by rw [finrank_eigenspace_comparison f, finrank_eigenspace_L_neg_two], fun μ h6 h2 hm2 => ?_⟩
  have h := finrank_eigenspace_comparison f μ
  rw [eigenspace_L_other μ h6 h2 hm2, finrank_bot] at h
  exact Submodule.finrank_eq_zero.mp h

end CandidateSystem

end Comparison.System
