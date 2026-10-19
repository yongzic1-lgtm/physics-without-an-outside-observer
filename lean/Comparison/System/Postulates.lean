import Comparison.System.Basic

/-!
# The proof system, part 1: the five postulates and the uniqueness theorem

The five postulates in their mathematical form
(main text, Sections III and IV), as Lean definitions, and the theorem that ties every consequence
to
them: **a system that satisfies the mathematical form of P1 to P3 is the quaternionic plane, four
complex amplitudes and five directions**, stated for every candidate system.

* **P1** (`P1.IsState`, `P1.IsMixedState`, `P1.IsOutcomes`, `P1.chance`, `P1.TwoThings`): a system
  is a
  finite-dimensional complex Hilbert space `H`; two systems are `H ⊗ H`; the chances `Tr(ρF_r)` of a
  complete family of outcomes add to one (`P1.chance_sum`).
* **P2** (`P2a`, `P2b`): on the operators of two systems, kept by every `U ⊗ U` with `U ∈ Sp(2)` and
  by the
  exchange; kept by the quaternionic structure taken on one system. The comparison satisfies both (`comparison_P2`).
* **P3** (`Partner`, `Partner.IsDistinctionH`, `Partner.P3H`): the quaternionic structure and the distinctions.
* **P1 to P3 together** (`CandidateSystem`), the model (`modelSystem`), the distinctions of a system
  (`CandidateSystem.Q`), and its gauges (`CandidateSystem.Frame`, Definition 24).
* **The uniqueness theorem** (`uniqueness`): for every candidate system `S`, `dim_ℂ H = 4`,
  `dim_ℝ Q = 5`, a gauge exists, in every gauge the five directions are distinctions with
  `{γ_s, γ_t} = 2δ_st` and product one that form a basis of `Q`, two gauges differ by one rotation of
  `Sp(2)`, and `i`, `Θ` anticommute (the quaternionic plane, real dimension 8).
  `systems_isomorphic`: any two candidate systems are isomorphic.
* **P4** (`IsFact`, with `Connection`, `Connection.rename`, `hol`): only closed comparisons are
  facts
  (`trace_hol_closed_isFact`).
* **P5** (`step`, `IsHistory`, `relationOf`, `LineState`): one step at each moment, one of the five
  directions on one system; never the same step twice in a row; the two-spinor state to an earlier moment is the
  product of the steps between.

How a theorem cites the uniqueness theorem: a general statement is proved for every `S` (directly,
or
through a gauge `f : S.Frame` and the star-algebra isomorphism `f.conj` that carries the model's
theorem); a statement about the model is proved about the model.
-/

namespace Comparison.System

open Matrix Complex
open scoped InnerProductSpace TensorProduct Kronecker

/-! ## P1: a system is a finite-dimensional complex Hilbert space -/

namespace P1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A state** of a system: a unit vector of `H` (Definition 2). -/
def IsState (v : H) : Prop := ‖v‖ = 1

/-- **A mixed state**: a positive operator of trace one (Definition 2). -/
def IsMixedState (ρ : H →ₗ[ℂ] H) : Prop := ρ.IsPositive ∧ LinearMap.trace ℂ H ρ = 1

/-- **A complete family of outcomes**: positive operators `F_r` with `Σ_r F_r = 1`. -/
def IsOutcomes {ι : Type*} [Fintype ι] (F : ι → H →ₗ[ℂ] H) : Prop :=
  (∀ r, (F r).IsPositive) ∧ ∑ r, F r = 1

/-- **The chance** of the outcome `F` in the mixed state `ρ`: `Tr(ρF)`. -/
noncomputable def chance (ρ F : H →ₗ[ℂ] H) : ℂ := LinearMap.trace ℂ H (ρ * F)

/-- **The chances of a complete family of outcomes add to one.** -/
theorem chance_sum {ι : Type*} [Fintype ι] {ρ : H →ₗ[ℂ] H} (hρ : IsMixedState ρ)
    {F : ι → H →ₗ[ℂ] H} (hF : IsOutcomes F) : ∑ r, chance ρ (F r) = 1 := by
  simp only [chance, ← map_sum, ← Finset.mul_sum, hF.2, mul_one, hρ.2]

/-- **Two systems together** have the space `H ⊗ H`, with the inner product of the tensor product,
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫⟪b, d⟫`. -/
abbrev TwoThings (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H ⊗[ℂ] H

theorem inner_tmul (a b c d : H) :
    ⟪(a ⊗ₜ[ℂ] b : TwoThings H), c ⊗ₜ[ℂ] d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ :=
  TensorProduct.inner_tmul ℂ a c b d

end P1

/-! ## P2: all inside observers have equal right, one's own past among them -/

/-- **P2 (a)** on an operator of two systems of the model: one rotation `U ∈ Sp(2)` that keeps the
quaternionic structure,
carrying both systems at once, leaves it unchanged, and so does the exchange of the two systems. -/
def P2a (X : Matrix Two Two ℂ) : Prop :=
  (∀ U ∈ Sp2, ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ)) * X =
      X * ((U : Matrix Four Four ℂ) ⊗ₖ (U : Matrix Four Four ℂ))) ∧ swap * X = X * swap

/-- **P2 (b)**: comparing a system with its own past is comparing it with a neighbour: the quaternionic structure
taken on one of the two systems, `X ⊗ Y ↦ X ⊗ Y^♯`, leaves the operator unchanged. -/
def P2b (X : Matrix Two Two ℂ) : Prop := partnerTwo X = X

/-- **The comparison satisfies P2.** -/
theorem comparison_P2 : P2a L ∧ P2b L := by
  refine ⟨⟨fun U hU => ?_, ?_⟩, partnerTwo_L⟩
  · have hu : (U : Matrix Four Four ℂ) * (U : Matrix Four Four ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    have hJ : (U : Matrix Four Four ℂ) * J * (U : Matrix Four Four ℂ)ᵀ = J := hU
    exact (keeps_L_iff _ hu (det_eq_one_of_keeps_J _ hJ)).mpr (Or.inl hJ)
  · rw [L_eq_two_swap_Eop, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      ArticleStatements.swap_mul_Eop, ArticleStatements.Eop_mul_swap]

/-! ## P3, and P1 to P3 together: the candidate systems -/

/-- **A candidate system**: a system (P1: a finite-dimensional complex Hilbert space) with a quaternionic structure
(P3 (a)) whose distinctions satisfy P3 (b): some distinction is not zero, and every distinction
squares
to a number. -/
structure CandidateSystem where
  /-- The space of the states of the system. -/
  H : Type
  [instNormed : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  [instFinite : FiniteDimensional ℂ H]
  /-- The quaternionic structure, P3 (a). -/
  partner : Partner H
  /-- P3 (b). -/
  p3b : partner.P3H

attribute [instance] CandidateSystem.instNormed CandidateSystem.instInner
  CandidateSystem.instFinite

/-- **The model**: `ℂ⁴` with the quaternionic structure `Θ v = J₀ v̄`. -/
noncomputable def modelSystem : CandidateSystem where
  H := ModelH
  partner := modelPartner
  p3b := (modelPartner.one_model_general).mpr (by simp)

namespace CandidateSystem

variable (S : CandidateSystem)

theorem partner_zero : S.partner.Θ 0 = 0 := by
  have h := S.partner.map_smul 0 0
  simpa using h

/-- **The distinctions of `S`** (Definition 4), a real vector space. -/
def Q : Submodule ℝ (S.H →ₗ[ℂ] S.H) where
  carrier := {a | S.partner.IsDistinctionH a}
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨ha1.add hb1, by simp [ha2, hb2], fun v => ?_⟩
    simp only [LinearMap.add_apply, ha3, hb3, S.partner.map_add]
  zero_mem' := by
    refine ⟨IsSelfAdjoint.zero _, by simp, fun v => ?_⟩
    simp [S.partner_zero]
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    have hc : (c • a : S.H →ₗ[ℂ] S.H) = ((c : ℂ) • a) := by
      ext v
      simp [Complex.coe_smul]
    rw [Set.mem_ofPred_eq, hc]
    refine ⟨?_, by simp [ha2], fun v => ?_⟩
    · exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) ha1
    · simp only [LinearMap.smul_apply, ha3, S.partner.map_smul, Complex.star_def,
        Complex.conj_ofReal]

theorem mem_Q (a : S.H →ₗ[ℂ] S.H) : a ∈ S.Q ↔ S.partner.IsDistinctionH a := Iff.rfl

/-- **A gauge of the system** (Definition 24): an orthonormal basis `u₁, −Θu₁, u₂, −Θu₂` in which
the
quaternionic structure has the matrix `J₀`. -/
structure Frame where
  /-- The basis, indexed by the four amplitudes. -/
  b : OrthonormalBasis Four ℂ S.H
  /-- The basis is normal for the quaternionic structure. -/
  normal : ∀ k : Fin 2, b (k, 1) = -S.partner.Θ (b (k, 0))

variable {S}

namespace Frame

variable (f : S.Frame)

/-- The coordinates of a gauge, a unitary map onto the model. -/
noncomputable def e : S.H ≃ₗᵢ[ℂ] ModelH := f.b.repr

theorem e_apply (v : S.H) (p : Four) : f.e v p = ⟪f.b p, v⟫_ℂ := f.b.repr_apply_apply v p

/-- **A gauge carries the quaternionic structure to `J₀K`.** -/
theorem e_partner (v : S.H) : f.e (S.partner.Θ v) = modelΘ (f.e v) := by
  ext p
  rw [e_apply, modelΘ_apply, S.partner.coord_Θ f.b f.normal v p, Jn_two_eq]
  congr 2
  funext q
  rw [Pi.star_apply]
  exact congrArg star (f.e_apply v q).symm

theorem e_symm_partner (w : ModelH) : f.e.symm (modelΘ w) = S.partner.Θ (f.e.symm w) := by
  apply f.e.injective
  rw [LinearIsometryEquiv.apply_symm_apply, e_partner, LinearIsometryEquiv.apply_symm_apply]

/-- **The matrix of an operator in a gauge**, a star-algebra isomorphism. -/
noncomputable def conj : (S.H →ₗ[ℂ] S.H) ≃⋆ₐ[ℂ] Matrix Four Four ℂ :=
  LinearMap.toMatrixOrthonormal f.b

theorem conj_apply (a : S.H →ₗ[ℂ] S.H) (p q : Four) : f.conj a p q = ⟪f.b p, a (f.b q)⟫_ℂ :=
  LinearMap.toMatrixOrthonormal_apply_apply f.b a p q

/-- **In a gauge, a distinction of `S` is a distinction of the model.** -/
theorem mem_Q_iff (a : S.H →ₗ[ℂ] S.H) : a ∈ S.Q ↔ IsDistinction (f.conj a) :=
  S.partner.isDistinctionH_iff f.b f.normal a

/-- **The five directions of `S` in the gauge `f`:** `f.e⁻¹ γ_s f.e`. -/
noncomputable def lines (s : Fin 5) : S.H →ₗ[ℂ] S.H := f.conj.symm (γ s)

theorem conj_injective : Function.Injective f.conj := f.conj.injective

theorem conj_lines (s : Fin 5) : f.conj (f.lines s) = γ s := f.conj.apply_symm_apply _

theorem lines_mem_Q (s : Fin 5) : f.lines s ∈ S.Q := by
  rw [f.mem_Q_iff, f.conj_lines]
  exact γ_isDistinction s

theorem lines_clifford (s t : Fin 5) :
    f.lines s * f.lines t + f.lines t * f.lines s =
      (if s = t then (2 : ℂ) else 0) • (1 : S.H →ₗ[ℂ] S.H) := by
  apply f.conj_injective
  simp only [map_add, map_mul, map_smul, map_one, f.conj_lines]
  exact clifford s t

theorem lines_prod : f.lines 0 * f.lines 1 * f.lines 2 * f.lines 3 * f.lines 4 = 1 := by
  apply f.conj_injective
  simp only [map_mul, map_one, f.conj_lines]
  exact γ_prod

/-- The coordinates of an operator along the five directions of a gauge. -/
noncomputable def coords (a : S.H →ₗ[ℂ] S.H) : Fin 5 → ℝ := coord (f.conj a)

/-- **Every distinction is `Σ t_s γ_s` in the lines of a gauge, with unique real `t`.** -/
theorem distinction_basis (a : S.H →ₗ[ℂ] S.H) (ha : a ∈ S.Q) :
    ∃! t : Fin 5 → ℝ, a = ∑ s, (t s : ℂ) • f.lines s := by
  have hd := (f.mem_Q_iff a).mp ha
  have hsum : ∀ t : Fin 5 → ℝ, f.conj (∑ s, (t s : ℂ) • f.lines s) = ∑ s, (t s : ℂ) • γ s := by
    intro t
    simp only [map_sum, map_smul, f.conj_lines]
  refine ⟨f.coords a, ?_, fun t ht => ?_⟩
  · apply f.conj_injective
    rw [hsum]
    exact eq_sum_coord _ hd
  · have h := congrArg f.conj ht
    rw [hsum] at h
    rw [coords, h, coord_sum]

/-- The real-linear coordinates of the distinctions in a gauge. -/
noncomputable def coordsQ : S.Q ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun a := f.coords a
  invFun t := ⟨∑ s, (t s : ℂ) • f.lines s, by
    refine S.Q.sum_mem fun s _ => ?_
    have h : ((t s : ℂ) • f.lines s : S.H →ₗ[ℂ] S.H) = (t s) • f.lines s := by
      ext v
      simp [Complex.coe_smul]
    rw [h]
    exact S.Q.smul_mem _ (f.lines_mem_Q s)⟩
  map_add' a b := by
    funext s
    simp only [coords, coord, Submodule.coe_add, map_add, Matrix.add_mul, τ, Matrix.trace_add,
      add_div, Complex.add_re, Pi.add_apply]
  map_smul' c a := by
    funext s
    have h : ((c • a : S.Q) : S.H →ₗ[ℂ] S.H) = (c : ℂ) • (a : S.H →ₗ[ℂ] S.H) := by
      ext v
      simp [Complex.coe_smul]
    simp only [coords, coord, h, map_smul, Matrix.smul_mul, τ, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply, Pi.smul_apply]
    rw [mul_div_assoc, Complex.re_ofReal_mul]
  left_inv a := by
    apply Subtype.ext
    obtain ⟨t, ht, -⟩ := f.distinction_basis a a.2
    simp only
    have hc : f.coords a = t := by
      rw [coords, ht]
      simp only [map_sum, map_smul, f.conj_lines, coord_sum]
    rw [hc, ← ht]
  right_inv t := by
    simp only [coords, map_sum, map_smul, f.conj_lines, coord_sum]

end Frame

end CandidateSystem

open CandidateSystem

/-- **Every candidate system has a gauge.** The normal basis of the quaternionic structure (Prop. 1) has `n = 2`
quaternionic dimensions by P3 (b) (Prop. 3). -/
theorem exists_frame (S : CandidateSystem) : Nonempty S.Frame := by
  obtain ⟨n, b, hb⟩ := S.partner.exists_normal_basis
  have hn : n = 2 := (one_model n).mp ((S.partner.P3H_iff b hb).mp S.p3b)
  subst hn
  exact ⟨⟨b, hb⟩⟩

/-- **Two gauges differ by one rotation of `Sp(2)`.** -/
theorem frames_differ {S : CandidateSystem} (f f' : S.Frame) :
    ∃ U ∈ Sp2, ∀ w : ModelH, f'.e (f.e.symm w) =
      WithLp.toLp 2 ((U : Matrix Four Four ℂ) *ᵥ WithLp.ofLp w) := by
  set M : Matrix Four Four ℂ := Matrix.of fun p q => ⟪f'.b p, f.b q⟫_ℂ with hM
  have hMw : ∀ w : ModelH, f'.e (f.e.symm w) = WithLp.toLp 2 (M *ᵥ WithLp.ofLp w) := by
    intro w
    ext p
    rw [Frame.e_apply, Frame.e, ← f.b.sum_repr_symm w]
    simp only [inner_sum, inner_smul_right, hM, Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hunit : M * star M = 1 := by
    ext p r
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := f.b.sum_inner_mul_inner (f'.b p) (f'.b r)
    have e : ∀ x, M p x * star M x r = ⟪f'.b p, f.b x⟫_ℂ * ⟪f.b x, f'.b r⟫_ℂ := by
      intro x
      simp only [hM, Matrix.star_apply, Matrix.of_apply]
      rw [← inner_conj_symm (f.b x) (f'.b r)]
      rfl
    simp only [e, h]
    exact orthonormal_iff_ite.mp f'.b.orthonormal p r
  set U : Matrix.unitaryGroup Four ℂ := ⟨M, Matrix.mem_unitaryGroup_iff.mpr hunit⟩ with hU
  refine ⟨U, ?_, hMw⟩
  rw [mem_Sp2_iff_keeps_partner]
  intro v
  have h1 := hMw (WithLp.toLp 2 (Θ v))
  have h2 := hMw (WithLp.toLp 2 v)
  have h3 : WithLp.toLp 2 (Θ v) = modelΘ (WithLp.toLp 2 v) := rfl
  rw [h3, f.e_symm_partner, f'.e_partner, h2] at h1
  have h4 := congrArg (WithLp.ofLp (p := 2)) h1
  simpa [modelΘ] using h4.symm

/-- **The uniqueness theorem.** A system that satisfies the mathematical form of P1 to P3 is the
quaternionic plane: four complex amplitudes, five directions. For every candidate system `S`:
`dim_ℂ H = 4`; `dim_ℝ Q = 5`; `S` has a gauge, a unitary map onto the model that carries its
conjugate
to `J₀K`; in every gauge the five directions are distinctions with `{γ_s, γ_t} = 2δ_st` and product one,
and every distinction is `Σ t_s γ_s` with unique real `t`; two gauges differ by one rotation of
`Sp(2)`;
and `Θ i = −i Θ`, so `i`, `Θ`, `iΘ` are the quaternion units and `H` has real dimension 8. -/
theorem uniqueness (S : CandidateSystem) :
    Module.finrank ℂ S.H = 4 ∧
    Module.finrank ℝ S.Q = 5 ∧
    Nonempty S.Frame ∧
    (∀ f : S.Frame, (∀ s, f.lines s ∈ S.Q) ∧
      (∀ s t, f.lines s * f.lines t + f.lines t * f.lines s =
        (if s = t then (2 : ℂ) else 0) • (1 : S.H →ₗ[ℂ] S.H)) ∧
      f.lines 0 * f.lines 1 * f.lines 2 * f.lines 3 * f.lines 4 = 1 ∧
      (∀ a ∈ S.Q, ∃! t : Fin 5 → ℝ, a = ∑ s, (t s : ℂ) • f.lines s)) ∧
    (∀ f f' : S.Frame, ∃ U ∈ Sp2, ∀ w : ModelH, f'.e (f.e.symm w) =
      WithLp.toLp 2 ((U : Matrix Four Four ℂ) *ᵥ WithLp.ofLp w)) ∧
    (∀ v : S.H, S.partner.Θ (Complex.I • v) = -(Complex.I • S.partner.Θ v)) ∧
    Module.finrank ℝ S.H = 8 := by
  obtain ⟨f⟩ := exists_frame S
  have h4 : Module.finrank ℂ S.H = 4 := by
    rw [f.e.toLinearEquiv.finrank_eq, finrank_euclideanSpace]
    rfl
  refine ⟨h4, ?_, ⟨f⟩, fun g => ⟨g.lines_mem_Q, g.lines_clifford, g.lines_prod,
    g.distinction_basis⟩, frames_differ, fun v => ?_, ?_⟩
  · rw [f.coordsQ.finrank_eq, Module.finrank_fin_fun]
  · rw [S.partner.map_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · rw [← Module.finrank_mul_finrank ℝ ℂ S.H, Complex.finrank_real_complex, h4]

/-- **Any two candidate systems are the same up to a unitary map that carries quaternionic structure to quaternionic structure.**
-/
theorem systems_isomorphic (S S' : CandidateSystem) :
    ∃ e : S.H ≃ₗᵢ[ℂ] S'.H, ∀ v, e (S.partner.Θ v) = S'.partner.Θ (e v) := by
  obtain ⟨f⟩ := exists_frame S
  obtain ⟨f'⟩ := exists_frame S'
  refine ⟨f.e.trans f'.e.symm, fun v => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, f.e_partner, f'.e_symm_partner]

/-! ## P4: only closed comparisons are facts -/

/-- **P4:** a number read from a connection is a fact exactly when no gauge transformation changes it.
-/
def IsFact {X G α : Type*} [Group G] (F : Connection X G → α) : Prop :=
  ∀ (c : Connection X G) (g : X → G), F (c.rename g) = F c

/-- **The trace of the holonomy of a closed walk is a fact** (Prop. 32), for every group of
invertible matrices. -/
theorem trace_hol_closed_isFact {X : Type*} {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (x : X) (rest : List X) (hclosed : (x :: rest).getLast (List.cons_ne_nil x rest) = x) :
    IsFact (fun c : Connection X (Matrix n n R)ˣ =>
      ((hol c (x :: rest) : (Matrix n n R)ˣ) : Matrix n n R).trace) := by
  intro c g
  exact trace_hol_isFact c g x rest hclosed

/-- The matrix of a rotation of `Sp(2)`. -/
abbrev turnMatrix (U : Sp2) : Matrix Four Four ℂ := GroupsContinuumLaw.mat U

/-- **P4 on the sixteen vertices, with the rotations of `Sp(2)`:** the trace of the holonomy of a closed
walk is a fact. -/
theorem trace_hol_Sp2_isFact (x : Fin 16) (rest : List (Fin 16))
    (hclosed : (x :: rest).getLast (List.cons_ne_nil x rest) = x) :
    IsFact (fun c : Connection (Fin 16) Sp2 => (turnMatrix (hol c (x :: rest))).trace) := by
  intro c g
  simp only [turnMatrix, hol_rename_closed c g x rest hclosed, GroupsContinuumLaw.mat_mul, GroupsContinuumLaw.mat_inv]
  rw [Matrix.trace_mul_cycle, GroupsContinuumLaw.sp2_unitary', Matrix.one_mul]

/-! ## P5: to exist is to persist from step to step -/

/-- **P5 (a):** a world line takes one step at each moment, one of its five lines;
`t k` is its step at the moment `k + 1`. -/
abbrev Steps := ℕ → Fin 5

/-- **P5 (b):** a line is compared only with its own previous moment, and each step changes that
two-spinor state: the same step is never taken twice in a row. -/
def ChangesEachStep (t : Steps) : Prop := ∀ k, t (k + 1) ≠ t k

/-- **P5 (c):** the two-spinor state of a line at the moment `k` to its start is the product of the steps
between, on the sixteen two-spinor states. -/
def relAt (t : Steps) : ℕ → Fin 16
  | 0 => 0
  | k + 1 => transition (t k) (relAt t k)

/-- The state of a line after its step `t k`: its two-spinor state to its start and its last-step direction. -/
def stateAt (t : Steps) (k : ℕ) : State := (relAt t (k + 1), t k)

/-- **Under P5 every next state is a continuation of the state before** (`B`'s entry is one):
the next step depends only on the state, the two-spinor state and the last-step direction. -/
theorem stateAt_continues (t : Steps) (ht : ChangesEachStep t) (k : ℕ) :
    Continues (stateAt t k) (stateAt t (k + 1)) := ⟨ht k, rfl⟩

theorem B_stateAt (R : Type*) [CommRing R] (t : Steps) (ht : ChangesEachStep t) (k : ℕ) :
    B R (stateAt t (k + 1)) (stateAt t k) = 1 := by
  simp [B_apply, stateAt_continues t ht k]

/-- **P5 (a):** a step is one of the five directions applied to one system; on the sixteen two-spinor states it is
the transition `x ↦ x ⊕ g_t` (Prop. 14). -/
abbrev step (t : Fin 5) : Fin 16 → Fin 16 := transition t

/-- **P5 (b):** a walk never takes the same step twice in a row: each step changes the two-spinor state
with its own previous moment, and never undoes its last change at once. -/
abbrev IsHistory (w : List (Fin 5)) : Prop := Reduced w

/-- **P5 (c):** the two-spinor state of a line to its start is the product of the steps between. -/
abbrev relationOf (w : List (Fin 5)) : Fin 16 := relOfWord w

/-- **The state of a line:** its two-spinor state together with the change that led to it (Prop. 26). -/
abbrev LineState := State

end Comparison.System
