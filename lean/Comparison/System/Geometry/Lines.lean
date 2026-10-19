import Comparison.System.Geometry.OneThing

/-!
# The geometry of comparison, Book I continued: lines, sides, rotations, overlap, sphere (Props. 4 to 8)

* `prop_4`: for every candidate system, `ab + ba = 2τ(ab)·1` on `Q`; on the model the five directions
  satisfy `γ_sγ_t + γ_tγ_s = 2δ_st`, and for **every** orthonormal basis `m₁, …, m₅` of `Q`
  `γ(m₁)⋯γ(m₅) = det(m)·1 = ±1`.
* `prop_5`: the two sides `Q_{±n}` are complementary projectors of rank two kept by the quaternionic structure; the
  one, the five directions and the ten `iγ_sγ_t` are an orthonormal real basis of the observables.
* `prop_6`: `Sp(2) = {U : UΘ = ΘU} = {U : UJUᵀ = J}`, `UΓ(n)U† = γ(Rn)`, onto `SO(5)` with kernel `±1`,
  ten generators.
* `prop_7`: `Q_nQ_mQ_n = ((1 + n·m)/2)Q_n = cos²(∠/2)Q_n`, and the chance of a state.
* `prop_8`: the lines are `S⁴`, the sides are the quaternionic lines (`S⁴ = ℍP¹`), the twistor map
  `ψ ↦ n(ψ)` with fibre `span{ψ, Θψ}`.
-/

open scoped InnerProductSpace Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## Proposition 4 -/

/-- **Polarization of P3 (b):** on every system whose distinctions square to numbers,
`ab + ba = 2τ(ab)·1` for all distinctions `a, b`. -/
theorem anticomm_of_P3H {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : Partner H) (hT : T.P3H) {a b : H →ₗ[ℂ] H}
    (ha : T.IsDistinctionH a) (hb : T.IsDistinctionH b) :
    a * b + b * a = (2 * τH (a * b)) • (1 : H →ₗ[ℂ] H) := by
  obtain ⟨-, hsq⟩ := (P3H_iff_tau T).mp hT
  have hab : T.IsDistinctionH (a + b) := (distinctionsH T).add_mem ha hb
  have e1 := hsq (a + b) hab
  have e2 := hsq a ha
  have e3 := hsq b hb
  have hcomm : τH (b * a) = τH (a * b) := by
    simp only [τH, LinearMap.trace_mul_comm ℂ b a]
  have hexp : (a + b) * (a + b) = a * a + (a * b + b * a) + b * b := by noncomm_ring
  have hτ : τH ((a + b) * (a + b)) = τH (a * a) + (τH (a * b) + τH (b * a)) + τH (b * b) := by
    simp only [τH, hexp, map_add, add_div]
  calc a * b + b * a = (a + b) * (a + b) - a * a - b * b := by noncomm_ring
    _ = τH ((a + b) * (a + b)) • (1 : H →ₗ[ℂ] H) - τH (a * a) • 1 - τH (b * b) • 1 := by
        rw [← e1, ← e2, ← e3]
    _ = (2 * τH (a * b)) • (1 : H →ₗ[ℂ] H) := by
        rw [hτ, hcomm]
        module

/-- On the model, `τ(γ(n)γ(m)) = n·m`. -/
theorem τ_gamma_mul (n m : Fin 5 → ℝ) : τ (gamma n * gamma m) = ((∑ s, n s * m s : ℝ) : ℂ) := by
  have h := anticomm_γv n m
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_add, Matrix.trace_mul_comm (γv m), Matrix.trace_smul, Matrix.trace_one] at ht
  simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at ht
  have : (γv n * γv m).trace = 4 * ((∑ s, n s * m s : ℝ) : ℂ) := by
    push_cast at ht ⊢
    linear_combination ht / 2
  show (γv n * γv m).trace / 4 = _
  rw [this]
  ring

/-- **On the model, `ab + ba = 2τ(ab)·1` for all distinctions.** -/
theorem anticomm_distinction {a b : Matrix Four Four ℂ} (ha : IsDistinction a)
    (hb : IsDistinction b) : a * b + b * a = (2 * τ (a * b)) • (1 : Matrix Four Four ℂ) := by
  have ea := eq_sum_coord a ha
  have eb := eq_sum_coord b hb
  have hga : a = gamma (coord a) := ea
  have hgb : b = gamma (coord b) := eb
  rw [hga, hgb, anticomm_γv, τ_gamma_mul]
  push_cast
  rfl

/-- The coordinate vector `m i` of an orthonormal family, as a point of `E5`. -/
noncomputable def frameVec (m : Fin 5 → Fin 5 → ℝ) (i : Fin 5) : GroupsContinuumLaw.E5 :=
  WithLp.toLp 2 (m i)

theorem frame_orthonormal (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) : Orthonormal ℝ (frameVec m) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [GroupsContinuumLaw.inner_E5]
  simpa [frameVec] using hm i j

/-- The orthonormal basis made of an orthonormal family of five vectors of `ℝ⁵`. -/
noncomputable def frameBasis (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) :
    OrthonormalBasis (Fin 5) ℝ GroupsContinuumLaw.E5 :=
  OrthonormalBasis.mk (frame_orthonormal m hm) (by
    have h := (frame_orthonormal m hm).linearIndependent
    have hspan := h.span_eq_top_of_card_eq_finrank' (by simp)
    rw [hspan])

theorem frameBasis_apply (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) (i : Fin 5) :
    frameBasis m hm i = frameVec m i := by
  simp [frameBasis]

/-- The rotation (or reflection) of `ℝ⁵` that carries the standard basis to the family `m`. -/
noncomputable def frameIso (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) :
    GroupsContinuumLaw.E5 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E5 :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).repr.trans (frameBasis m hm).repr.symm

theorem frameIso_single (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) (i : Fin 5) :
    frameIso m hm (EuclideanSpace.single i 1) = frameVec m i := by
  rw [frameIso, LinearIsometryEquiv.trans_apply]
  have : (EuclideanSpace.basisFun (Fin 5) ℝ).repr (EuclideanSpace.single i 1) =
      EuclideanSpace.single i 1 := by
    ext j
    simp [EuclideanSpace.basisFun_repr]
  rw [this, OrthonormalBasis.repr_symm_single, frameBasis_apply]

/-- **The determinant of the frame map is `det m`.** -/
theorem det_frameIso (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) :
    LinearMap.det (frameIso m hm).toLinearMap = (Matrix.of m).det := by
  have hlin : (frameIso m hm).toLinearMap =
      Matrix.toLin GroupsContinuumLaw.b5 GroupsContinuumLaw.b5 (Matrix.of m)ᵀ := by
    apply GroupsContinuumLaw.b5.ext
    intro j
    rw [Matrix.toLin_self]
    have hb : GroupsContinuumLaw.b5 j = EuclideanSpace.single j 1 := by simp
    show frameIso m hm (GroupsContinuumLaw.b5 j) = _
    rw [hb, frameIso_single]
    ext s
    simp [frameVec, Matrix.transpose_apply, Finset.sum_apply, Pi.single_apply, hb]
  rw [hlin, LinearMap.det_toLin, Matrix.det_transpose]

theorem gamma_frameVec_conj (U : GroupsContinuumLaw.Sp2) (x : GroupsContinuumLaw.E5) :
    GroupsContinuumLaw.gE (GroupsContinuumLaw.rotV U x) =
      GroupsContinuumLaw.mat U * GroupsContinuumLaw.gE x * star (GroupsContinuumLaw.mat U) := GroupsContinuumLaw.sp2_conj_line U x

theorem prod_conj (A : Matrix Four Four ℂ) (hA : star A * A = 1) (g : Fin 5 → Matrix Four Four ℂ) :
    (A * g 0 * star A) * (A * g 1 * star A) * (A * g 2 * star A) * (A * g 3 * star A) *
        (A * g 4 * star A) = A * (g 0 * g 1 * g 2 * g 3 * g 4) * star A := by
  have hc : ∀ X : Matrix Four Four ℂ, star A * (A * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hc]

/-- **Five orthonormal lines multiply to `det(m)·1`:** for every orthonormal basis `m₁, …, m₅` of
`Q = ℝ⁵`, `γ(m₁)⋯γ(m₅) = det(m)·1`, which is `+1` for one orientation of the five and `−1` for
the other. -/
theorem gamma_frame_prod (m : Fin 5 → Fin 5 → ℝ)
    (hm : ∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) :
    gamma (m 0) * gamma (m 1) * gamma (m 2) * gamma (m 3) * gamma (m 4) =
      (((Matrix.of m).det : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) ∧
    ((Matrix.of m).det = 1 ∨ (Matrix.of m).det = -1) := by
  set φ := frameIso m hm with hφ
  have hdet := det_frameIso m hm
  have hpm := GroupsContinuumLaw.det_isometry_pm φ
  rw [← hφ] at hdet
  have hg : ∀ i, gamma (m i) = GroupsContinuumLaw.gE (φ (EuclideanSpace.single i 1)) := by
    intro i
    rw [hφ, frameIso_single, gE_eq_gamma]
    rfl
  have hγ : γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 := γ_prod
  rcases hpm with h1 | h1
  · obtain ⟨U, hU⟩ := GroupsContinuumLaw.rot_onto φ h1
    have hU' : ∀ i, gamma (m i) = GroupsContinuumLaw.mat U * γ i * star (GroupsContinuumLaw.mat U) := by
      intro i
      rw [hg i, ← hU, GroupsContinuumLaw.rotHom_apply, GroupsContinuumLaw.sp2_conj_line, GroupsContinuumLaw.gE_single]
    refine ⟨?_, Or.inl (by rw [← hdet, h1])⟩
    rw [hU' 0, hU' 1, hU' 2, hU' 3, hU' 4,
      prod_conj (GroupsContinuumLaw.mat U) (GroupsContinuumLaw.sp2_unitary' U) γ, hγ, Matrix.mul_one,
      GroupsContinuumLaw.sp2_unitary, ← hdet, h1]
    simp
  · -- compose with the reflection of the first line
    set ρ : GroupsContinuumLaw.E5 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E5 := (ℝ ∙ (EuclideanSpace.single 0 1 : GroupsContinuumLaw.E5))ᗮ.reflection
    have hρdet : LinearMap.det ρ.toLinearMap = -1 :=
      GroupsContinuumLaw.det_reflection_ne (by simp : (EuclideanSpace.single 0 1 : GroupsContinuumLaw.E5) ≠ 0)
    have hdet' : LinearMap.det (φ * ρ).toLinearMap = 1 := by
      rw [GroupsContinuumLaw.det_mul_isometry, h1, hρdet]; norm_num
    obtain ⟨U, hU⟩ := GroupsContinuumLaw.rot_onto (φ * ρ) hdet'
    have hρ0 : ρ (EuclideanSpace.single 0 1) = -EuclideanSpace.single 0 1 := by
      rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
      simp
      module
    have hρs : ∀ i : Fin 5, i ≠ 0 → ρ (EuclideanSpace.single i 1) = EuclideanSpace.single i 1 := by
      intro i hi
      apply Submodule.reflection_mem_subspace_eq_self
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [EuclideanSpace.inner_single_left, PiLp.single_apply, hi]
    have hconj : ∀ x, GroupsContinuumLaw.gE ((φ * ρ) x) =
        GroupsContinuumLaw.mat U * GroupsContinuumLaw.gE x * star (GroupsContinuumLaw.mat U) := by
      intro x
      rw [← hU, GroupsContinuumLaw.rotHom_apply, GroupsContinuumLaw.sp2_conj_line]
    have h0 : gamma (m 0) = -(GroupsContinuumLaw.mat U * γ 0 * star (GroupsContinuumLaw.mat U)) := by
      have := hconj (EuclideanSpace.single 0 1)
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hρ0, map_neg,
        GroupsContinuumLaw.gE_neg, GroupsContinuumLaw.gE_single, ← hg 0] at this
      rw [← neg_neg (gamma (m 0)), this]
    have hs : ∀ i : Fin 5, i ≠ 0 → gamma (m i) = GroupsContinuumLaw.mat U * γ i * star (GroupsContinuumLaw.mat U) := by
      intro i hi
      have := hconj (EuclideanSpace.single i 1)
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hρs i hi, GroupsContinuumLaw.gE_single,
        ← hg i] at this
      exact this
    refine ⟨?_, Or.inr (by rw [← hdet, h1])⟩
    rw [h0, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide)]
    have := prod_conj (GroupsContinuumLaw.mat U) (GroupsContinuumLaw.sp2_unitary' U) γ
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, this, hγ, Matrix.mul_one,
      GroupsContinuumLaw.sp2_unitary, ← hdet, h1]
    simp

/-! ## Proposition 5 -/

open LinearMap in
/-- **Each side of a line has two dimensions:** `rank Q_n = 2`. -/
theorem rank_side (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) : (side n).rank = 2 := by
  have hid : IsIdempotentElem (Matrix.toLin' (side n)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, side_mul_self n hn]
  have htr := hid.isProj_range.trace
  rw [Matrix.trace_toLin'_eq, trace_side] at htr
  rw [Matrix.rank, ← Matrix.toLin'_apply']
  exact_mod_cast htr.symm

end Geometry

open Comparison.System.Geometry

/-- **Proposition 4 (perpendicular lines anticommute).** For every candidate system, `ab + ba =
2τ(ab)·1` for all distinctions `a, b`; on the model the five directions satisfy
`γ_sγ_t + γ_tγ_s = 2δ_st` and `γ₀γ₁γ₂γ₃γ₄ = 1`, and for **every** orthonormal basis `m₁, …, m₅` of
`Q` the product `γ(m₁)⋯γ(m₅)` is `det(m)·1`, `1` for one orientation and `−1` for the other. Every
candidate system: `System.uniqueness`. Recognition: none. -/
theorem prop_4 :
    (∀ S : CandidateSystem, ∀ a ∈ S.Q, ∀ b ∈ S.Q,
      a * b + b * a = (2 * τH (a * b)) • (1 : S.H →ₗ[ℂ] S.H)) ∧
    (∀ a b : Matrix Four Four ℂ, IsDistinction a → IsDistinction b →
      a * b + b * a = (2 * τ (a * b)) • (1 : Matrix Four Four ℂ)) ∧
    (∀ s t : Fin 5, γ s * γ t + γ t * γ s = (if s = t then (2 : ℂ) else 0) • (1 : Matrix Four Four ℂ)) ∧
    γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 ∧
    (∀ m : Fin 5 → Fin 5 → ℝ, (∀ i j, ∑ s, m i s * m j s = if i = j then 1 else 0) →
      gamma (m 0) * gamma (m 1) * gamma (m 2) * gamma (m 3) * gamma (m 4) =
        (((Matrix.of m).det : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) ∧
      ((Matrix.of m).det = 1 ∨ (Matrix.of m).det = -1)) :=
  ⟨fun S a ha b hb => anticomm_of_P3H S.partner S.p3b ha hb, fun _ _ ha hb =>
    anticomm_distinction ha hb, clifford, γ_prod, gamma_frame_prod⟩

/-- **Proposition 5 (two equal sides and sixteen observables).** For every unit `n`: `Q_{±n}` are
projectors, `Q_nQ_{−n} = 0`, `Q_n + Q_{−n} = 1`, each of rank two, kept by the quaternionic structure; the one, the
five directions and the ten `iγ_sγ_t` are Hermitian, orthonormal for `τ`, and span the Hermitian
operators: `16 = 1 + 5 + 10`. Every candidate system: `System.uniqueness`. Recognition: none. -/
theorem prop_5 :
    (∀ n : Fin 5 → ℝ, ∑ s, n s ^ 2 = 1 →
      side n * side n = side n ∧ side (-n) * side (-n) = side (-n) ∧ side n * side (-n) = 0 ∧
      side n + side (-n) = 1 ∧ (side n).rank = 2 ∧ (side (-n)).rank = 2 ∧
      ∀ v, side n *ᵥ Θ v = Θ (side n *ᵥ v)) ∧
    (∀ k, (obs k)ᴴ = obs k) ∧
    (∀ k l, (obs k * obs l).trace = if k = l then 4 else 0) ∧
    Submodule.span ℝ (Set.range obs) = hermitian ∧ finrank ℝ hermitian = 16 := by
  refine ⟨fun n hn => ?_, obs_conjTranspose, trace_obs_mul, span_obs_eq_hermitian,
    finrank_hermitian⟩
  have hn' : ∑ s, (-n) s ^ 2 = 1 := by simpa using hn
  refine ⟨side_mul_self n hn, side_mul_self (-n) hn', side_mul_side_neg n hn, side_add_side_neg n,
    rank_side n hn, rank_side (-n) hn', ?_⟩
  exact (commutes_Θ_iff _).mpr (GroupsContinuumLaw.side_isQProj n hn).2.2.2

/-- **Proposition 6 (the ten rotations).** `Sp(2)`, the unitary rotations with `UJUᵀ = J`, are exactly the
unitary rotations that keep the quaternionic structure; they have determinant one, act on the lines by
`Uγ(x)U† = γ(R_U x)` with `R_U ∈ SO(5)`, every rotation of `SO(5)` is some `R_U`, and `R_U = 1`
exactly when `U = ±1`: `Sp(2)/{±1} = SO(5)`; the generators are the ten `γ_sγ_t`. Recognition: by
P2 (a) no number the geometry reports tells one line from another. -/
theorem prop_6 :
    (∀ U : Matrix.unitaryGroup Four ℂ, U ∈ Sp2 ↔
      ∀ v, (U : Matrix Four Four ℂ) *ᵥ Θ v = Θ ((U : Matrix Four Four ℂ) *ᵥ v)) ∧
    (∀ U : Matrix.unitaryGroup Four ℂ,
      U ∈ Sp2 ↔ (U : Matrix Four Four ℂ) * J * (U : Matrix Four Four ℂ)ᵀ = J) ∧
    (∀ U ∈ Sp2, (U : Matrix Four Four ℂ) * J * (U : Matrix Four Four ℂ)ᵀ = J ∧
      (U : Matrix Four Four ℂ).det = 1) ∧
    (∀ (U : Sp2) (x : GroupsContinuumLaw.E5), gamma (WithLp.ofLp (GroupsContinuumLaw.rotHom U x)) =
      GroupsContinuumLaw.mat U * gamma (WithLp.ofLp x) * star (GroupsContinuumLaw.mat U)) ∧
    (∀ U : Sp2, LinearMap.det (GroupsContinuumLaw.rotHom U).toLinearMap = 1) ∧
    (∀ φ : GroupsContinuumLaw.E5 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E5, LinearMap.det φ.toLinearMap = 1 →
      ∃ U : Sp2, GroupsContinuumLaw.rotHom U = φ) ∧
    (∀ U : Sp2, GroupsContinuumLaw.rotHom U = 1 ↔ GroupsContinuumLaw.mat U = 1 ∨ GroupsContinuumLaw.mat U = -1) ∧
    sp2 = Submodule.span ℝ (Set.range fun f : Fin 10 => gen (Sum.inr f)) ∧ finrank ℝ sp2 = 10 :=
  ⟨mem_Sp2_iff_keeps_partner, fun _ => Iff.rfl, fun U hU => ⟨hU, det_eq_one_of_keeps_J _ hU⟩,
    fun U x => GroupsContinuumLaw.sp2_conj_line U x, GroupsContinuumLaw.rot_det, GroupsContinuumLaw.rot_onto, GroupsContinuumLaw.rot_ker,
    sp2_eq_span, finrank_sp2⟩

/-- **Proposition 7 (the overlap of two sides).** For unit `n` and every `m`,
`Q_nQ_mQ_n = ((1 + n·m)/2)Q_n`; for unit `n`, `m` the number is `cos²(∠(n, m)/2)` and is the same
with `n` and `m` exchanged; for every state `ψ` on the plus side of `n` the chance
`⟨ψ, Q_mψ⟩` is `(1 + n·m)/2`. Recognition: Born's rule; the chance needs no order of the two lines. -/
theorem prop_7 :
    (∀ n m : Fin 5 → ℝ, ∑ s, n s ^ 2 = 1 →
      side n * side m * side n = (((1 + ∑ s, n s * m s) / 2 : ℝ) : ℂ) • side n) ∧
    (∀ n m : GroupsContinuumLaw.E5, ‖n‖ = 1 → ‖m‖ = 1 →
      (1 + inner ℝ n m) / 2 = Real.cos (InnerProductGeometry.angle n m / 2) ^ 2 ∧
      inner ℝ n m = inner ℝ m n) ∧
    (∀ (n m : Fin 5 → ℝ) (ψ : Four → ℂ), ∑ s, n s ^ 2 = 1 → normSq ψ = 1 →
      side n *ᵥ ψ = ψ → star ψ ⬝ᵥ (side m *ᵥ ψ) = (((1 + ∑ s, n s * m s) / 2 : ℝ) : ℂ)) := by
  refine ⟨fun n m hn => overlap n m hn, fun n m hn hm => ⟨?_, real_inner_comm m n⟩,
    fun n m ψ hn hψ hside => ?_⟩
  · rw [Real.cos_sq (InnerProductGeometry.angle n m / 2),
      show 2 * (InnerProductGeometry.angle n m / 2) = InnerProductGeometry.angle n m by ring,
      InnerProductGeometry.cos_angle, hn, hm]
    ring
  · have hH : (side n)ᴴ = side n := (GroupsContinuumLaw.side_isQProj n hn).1
    have h1 : star ψ ⬝ᵥ ψ = 1 := by rw [dot_self_eq, hψ, Complex.ofReal_one]
    calc star ψ ⬝ᵥ (side m *ᵥ ψ) = star (side n *ᵥ ψ) ⬝ᵥ (side m *ᵥ (side n *ᵥ ψ)) := by
          rw [hside]
      _ = star ψ ⬝ᵥ ((side n * side m * side n) *ᵥ ψ) := by
          rw [Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (((1 + ∑ s, n s * m s) / 2 : ℝ) : ℂ) := by
          rw [overlap n m hn, Matrix.smul_mulVec, hside, dotProduct_smul, h1, smul_eq_mul,
            mul_one]

/-- **Proposition 8 (the sphere of lines).** `γ(n)` is a line exactly when `|n| = 1`: the lines are
the unit sphere `S⁴` of `Q`; `n ↦ Q_n` is a bijection of `S⁴` onto the two-dimensional subspaces kept
by the quaternionic structure (`S⁴ = ℍP¹`); for every state `ψ`, `n(ψ) = (⟨ψ, γ_sψ⟩)_s` is a unit vector with
`Q_{n(ψ)} = |ψ⟩⟨ψ| + |Θψ⟩⟨Θψ|`, it depends on `ψ` only up to a factor, and two states have the same
line exactly when one lies in `span{ψ, Θψ}`: the fibre is `ℂP¹`. Recognition: Penrose's twistor
fibration, with the matrix `J` of the quaternionic structure a nondegenerate infinity twistor. -/
theorem prop_8 :
    (∀ n : Fin 5 → ℝ, gamma n * gamma n = 1 ↔ ∑ s, n s ^ 2 = 1) ∧
    (∀ n : Fin 5 → ℝ, ∑ s, n s ^ 2 = 1 → GroupsContinuumLaw.IsQProj (side n)) ∧
    (∀ P, GroupsContinuumLaw.IsQProj P → ∃ n : Fin 5 → ℝ, ∑ s, n s ^ 2 = 1 ∧ P = side n) ∧
    Function.Injective side ∧
    Nonempty ({n : Fin 5 → ℝ // ∑ s, n s ^ 2 = 1} ≃ {P : Matrix Four Four ℂ // GroupsContinuumLaw.IsQProj P}) ∧
    (∀ ψ : Four → ℂ, normSq ψ = 1 → ∑ s, lineOf ψ s ^ 2 = 1 ∧
      side (lineOf ψ) = vecMulVec ψ (star ψ) + vecMulVec (Θ ψ) (star (Θ ψ))) ∧
    (∀ (c : ℂ) (ψ : Four → ℂ) (s : Fin 5), lineOf (c • ψ) s = Complex.normSq c * lineOf ψ s) ∧
    (∀ ψ φ : Four → ℂ, normSq ψ = 1 → normSq φ = 1 →
      (lineOf φ = lineOf ψ ↔ ∃ a b : ℂ, φ = a • ψ + b • Θ ψ)) := by
  refine ⟨fun n => ?_, GroupsContinuumLaw.side_isQProj, GroupsContinuumLaw.qproj_eq_side, GroupsContinuumLaw.side_injective,
    ⟨GroupsContinuumLaw.sphereEquivHP1⟩, fun ψ hψ => ⟨lineOf_unit ψ hψ, GroupsContinuumLaw.side_lineOf ψ hψ⟩,
    GroupsContinuumLaw.lineOf_phase, GroupsContinuumLaw.fibre_iff⟩
  have h := γv_mul_self n
  show γv n * γv n = 1 ↔ _
  rw [h]
  constructor
  · intro h1
    have := congrFun (congrFun h1 (0, 0)) (0, 0)
    simp at this
    exact_mod_cast this
  · intro h1
    rw [h1]
    simp

end Comparison.System
