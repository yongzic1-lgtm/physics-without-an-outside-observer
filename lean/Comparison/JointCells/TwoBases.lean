import Comparison.Law.Returns

/-!
# The two pairings are one joint operator in two bases, and the change of basis exchanges the
# line's vertical transition for the step's parallel transport

The first pairing walks a line over its sixteen vertices: the step along `t` moves the vertex
`S ↦ S △ T_t` (`transition t`), the division its two-spinor state to its past holds changing by four lines
(Propositions 25, 26). The second pairing holds a meeting and walks the last-step direction: the step along `t`
weighs the meeting `U` by its agreement sign `ε_t(U)` (Proposition 130). Here the meetings are read as
what they are, the two-spinor states `e_U = (B_U ⊗ 1)Ω` with `B_U` one system's operator (`relOp`): the
sixteen `B_U` are all the operators of one system, and the step of one system along `t`, `γ_t = iJ_nJ_t`
(Proposition 37), carries them by conjugation, `B_U ↦ γ_t B_U γ_t = ε_t(U) B_U` (`γ_conj_relOp`):
that conjugation is the parallel transport of one system's frame by the step.

* `PhiL`: **`Φ(v) = Σ_U (𝒳 v)_U B_U`**, the character transform `𝒳` of Proposition 130 followed by
  reading each meeting as its operator; a linear map from the vectors on the sixteen vertices to the
  operators of one system.
* `Phi_transition`: **`Φ(X_t v) = γ_t Φ(v) γ_t`**: the vertex transition of the first pairing (vertical: the held
  division changes by four lines) is, in the second pairing's basis, the step's conjugation of one
  system's operators (parallel: the frame carried by the step).
* `relOp_gram`: `tr(B_jᴴ B_k) = 4 δ_jk`; `PhiL_injective`, `PhiL_bijective`, `PhiE`: `Φ` is a linear
  isomorphism, so the two are bases of one space.
* `contBC_mulVec`, `Phi80_contB`: on the eighty states, **`Φ₈₀(B w) = 𝕁(Φ₈₀ w)`** with `𝕁` the joint
  walk at the singlet, `(𝕁 v)_s = γ_s (Σ_{t ≠ s} v_t) γ_s` (`jointSinglet`): the line's walk `B` of the
  first pairing and the last-step direction's walk carrying one system's frame are one operator in two bases;
  `Phi80_bijective`.
* `jointSinglet_channel`: on the channel `a ⊗ B_k` the joint walk is the meeting's walk `K_{T_k}`
  (Proposition 130's blocks, now as the transport of `B_k`); `jointTwin`: at the singlet's counterpart `{n}` the same
  operator with the opposite sign, whose channels are the sixteen counterparts `K_{T_k^c}`.
* `four_kinds`: the sixteen channels of `𝕁` are the types `0|6` (the singlet) and `2|4` (the ten symmetric states and
  the five vector states); the sixteen channels of `−𝕁` are the types `1|5` (the five `{t}` and
  `{n}`) and `3|3` (the ten colour counterparts). So the one operator `𝕁` carries the four types, the
  meetings on `𝕁` and the counterparts on `−𝕁`, read at `u` and at `−u` (`law_twins`).
-/

open Comparison Matrix Kronecker
open Comparison.Law

namespace Comparison.JointCells.Bases

/-! ## The change of basis: vertices to one system's operators -/

/-- **`Φ(v) = Σ_U (𝒳 v)_U B_U`** as a linear map. -/
noncomputable def PhiL : (Fin 16 → ℂ) →ₗ[ℂ] Matrix Four Four ℂ where
  toFun v := ∑ U, (∑ x, charX ℂ x U * v x) • relOp U
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun U _ => ?_
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem PhiL_apply (v : Fin 16 → ℂ) :
    PhiL v = ∑ U, (∑ x, charX ℂ x U * v x) • relOp U := rfl

theorem transition_eq_iff (s : Fin 5) (x y : Fin 16) : x = transition s y ↔ y = transition s x := by
  constructor
  · intro h; rw [h, transition_transition]
  · intro h; rw [h, transition_transition]

/-- **The vertex transition is the step's conjugation:** `Φ(v ∘ transition_t) = γ_t Φ(v) γ_t`. -/
theorem Phi_transition (t : Fin 5) (v : Fin 16 → ℂ) :
    PhiL (fun x => v (transition t x)) = γ t * PhiL v * γ t := by
  rw [PhiL_apply, PhiL_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, γ_conj_relOp, smul_smul]
  congr 1
  have hinv : Function.Involutive (transition t) := transition_transition t
  rw [← Equiv.sum_comp hinv.toPerm]
  simp only [Function.Involutive.coe_toPerm, transition_transition, charX_transition]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [agreeSign, charSign]
  split_ifs <;> push_cast <;> ring

/-- The vertex transition on the sixteen vertices, `X_t`, as Proposition 130's `transitionK`. -/
theorem transitionK_mulVec (t : Fin 5) (v : Fin 16 → ℂ) :
    transitionK ℂ t *ᵥ v = fun x => v (transition t x) := by
  funext x
  simp only [transitionK, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (transition t x)]
  · simp [transition_transition]
  · intro y _ hy
    have h : ¬ x = transition t y := fun h => hy ((transition_eq_iff t x y).mp h)
    simp [h]
  · simp

/-- **Proposition 130 read through `Φ`:** `Φ(X_t v) = γ_t Φ(v) γ_t`. -/
theorem Phi_transitionK (t : Fin 5) (v : Fin 16 → ℂ) :
    PhiL (transitionK ℂ t *ᵥ v) = γ t * PhiL v * γ t := by
  rw [transitionK_mulVec, Phi_transition]

/-! ## `Φ` is an isomorphism: the sixteen operators of the two-spinor states are a basis -/

theorem relOpZ_gram : ∀ j k : Fin 16,
    ((relOpZ j)ᴴ * relOpZ k).trace = if j = k then 4 else 0 := by
  decide +kernel

theorem toComplex_semiconj :
    Function.Semiconj (GaussianInt.toComplex : GaussianInt → ℂ) star star := fun x =>
  GaussianInt.toComplex_star x

/-- **`tr(B_jᴴ B_k) = 4 δ_jk`.** -/
theorem relOp_gram (j k : Fin 16) :
    ((relOp j)ᴴ * relOp k).trace = if j = k then 4 else 0 := by
  have h := congrArg (fun z : GaussianInt => (z : ℂ)) (relOpZ_gram j k)
  rw [← relOpZ_map j, ← relOpZ_map k, ← conjTranspose_map _ toComplex_semiconj,
    ← Matrix.map_mul]
  have htr : ∀ M : Matrix Four Four GaussianInt,
      (M.map GaussianInt.toComplex).trace = ((M.trace : GaussianInt) : ℂ) := by
    intro M
    simp [Matrix.trace, Matrix.map_apply, map_sum]
  rw [htr, h]
  by_cases hjk : j = k
  · simp only [hjk, ↓reduceIte]
    exact map_ofNat GaussianInt.toComplex 4
  · simp only [hjk, ↓reduceIte, map_zero]

theorem trace_PhiL (j : Fin 16) (v : Fin 16 → ℂ) :
    ((relOp j)ᴴ * PhiL v).trace = 4 * ∑ x, charX ℂ x j * v x := by
  rw [PhiL_apply, Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, relOp_gram, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

theorem PhiL_injective : Function.Injective PhiL := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hc : ∀ U, ∑ x, charX ℂ x U * v x = 0 := by
    intro U
    have h := trace_PhiL U v
    rw [hv, Matrix.mul_zero, Matrix.trace_zero] at h
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h.symm).resolve_left h4
  funext y
  have hX := congrFun (congrFun (charX_mul_self ℂ) y)
  have e : v y = ∑ x, (charX ℂ * charX ℂ) y x * v x := by
    simp [charX_mul_self, Matrix.one_apply]
  rw [e]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Pi.zero_apply]
  refine Finset.sum_eq_zero fun U _ => ?_
  have : ∑ x, charX ℂ y U * charX ℂ U x * v x = charX ℂ y U * ∑ x, charX ℂ x U * v x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [charX_symm ℂ U x]
    ring
  rw [this, hc U, mul_zero]

theorem PhiL_bijective : Function.Bijective PhiL := by
  refine ⟨PhiL_injective, ?_⟩
  have hdim : Module.finrank ℂ (Fin 16 → ℂ) = Module.finrank ℂ (Matrix Four Four ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_matrix]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp PhiL_injective

/-- **`Φ` as a linear isomorphism:** the vertices and one system's operators are two bases of one
sixteen-dimensional space. -/
noncomputable def PhiE : (Fin 16 → ℂ) ≃ₗ[ℂ] Matrix Four Four ℂ :=
  LinearEquiv.ofBijective PhiL PhiL_bijective

/-! ## The eighty states: the line's walk is the joint walk at the singlet -/

/-- The line's four continuations on the eighty states, over `ℂ`. -/
noncomputable def contBC : Matrix State State ℂ := contB.map (fun q : ℚ => (q : ℂ))

theorem contBC_mulVec (w : State → ℂ) (x : Fin 16) (s : Fin 5) :
    (contBC *ᵥ w) (x, s) = ∑ t, (if s = t then (0 : ℂ) else 1) * w (transition s x, t) := by
  simp only [contBC, contB, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Continues]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => ?_)
  rw [Finset.sum_eq_single (transition s x)]
  · by_cases h : s = t
    · simp [h]
    · simp [h, transition_transition]
  · intro y _ hy
    have : ¬ x = transition s y := fun h' => hy ((transition_eq_iff s x y).mp h')
    simp [this]
  · simp

/-- The same operator as the law's `stepOp transitionMat` (Propositions 54, 131). -/
theorem contBC_eq : contBC = stepOp transitionMat := by
  rw [contBC, contB_eq_transitionShaped, stepOp_transitionMat_eq]
  ext p q
  simp only [transitionShaped, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- One system's operators carried along the last-step direction: `Φ₈₀(w)_t = Φ(w(·, t))`. -/
noncomputable def Phi80 (w : State → ℂ) : Fin 5 → Matrix Four Four ℂ :=
  fun t => PhiL (fun x => w (x, t))

/-- **The joint walk at the singlet, `𝕁`:** the last-step direction leaves `t` for every `s ≠ t`, and the step along `s`
carries one system's operators, `X ↦ γ_s X γ_s`. -/
noncomputable def jointSinglet (v : Fin 5 → Matrix Four Four ℂ) : Fin 5 → Matrix Four Four ℂ :=
  fun s => γ s * (∑ t, (if s = t then (0 : ℂ) else 1) • v t) * γ s

/-- **The two pairings are one operator in two bases:** `Φ₈₀(B w) = 𝕁(Φ₈₀ w)`. The line's walk on its
eighty states (first pairing, the vertex moved) is, through `Φ`, the last-step direction's walk carrying one system's
operators by the step (second pairing, the frame transported). -/
theorem Phi80_contB (w : State → ℂ) : Phi80 (contBC *ᵥ w) = jointSinglet (Phi80 w) := by
  funext s
  simp only [Phi80, jointSinglet]
  have h1 : (fun x => (contBC *ᵥ w) (x, s)) =
      ∑ t, (if s = t then (0 : ℂ) else 1) • (fun x => w (transition s x, t)) := by
    funext x
    rw [contBC_mulVec, Finset.sum_apply]
    rfl
  rw [h1, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, Phi_transition s (fun x => w (x, t)), Matrix.mul_smul, Matrix.smul_mul]

theorem Phi80_bijective : Function.Bijective Phi80 := by
  constructor
  · intro w w' h
    funext ⟨x, t⟩
    have := PhiL_injective (congrFun h t)
    exact congrFun this x
  · intro v
    refine ⟨fun p => (PhiE.symm (v p.2)) p.1, ?_⟩
    funext t
    simp only [Phi80]
    have : (fun x => (PhiE.symm (v t)) x) = PhiE.symm (v t) := rfl
    rw [this]
    exact PhiE.apply_symm_apply (v t)

/-! ## The channels: the sixteen meetings and the sixteen counterparts -/

/-- **A channel of the joint walk:** on `a ⊗ B_k` the joint walk at the singlet is the meeting's last-step direction
walk `K_{T_k} = θ_{T_k}(𝐉 − I)`. -/
theorem jointSinglet_channel (k : Fin 16) (a : Fin 5 → ℂ) :
    jointSinglet (fun t => a t • relOp k) =
      fun s => (patternK (R := ℂ) (disagreeSet k) *ᵥ a) s • relOp k := by
  funext s
  simp only [jointSinglet]
  have hsum : (∑ t, (if s = t then (0 : ℂ) else 1) • (a t • relOp k)) =
      (∑ t, (if s = t then (0 : ℂ) else 1) * a t) • relOp k := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
  rw [hsum, Matrix.mul_smul, Matrix.smul_mul, γ_conj_relOp, smul_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, patternK_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **At the singlet's counterpart `{n}` the joint walk is `−𝕁`**: every step weighs `ε_s(all five) = −1`. -/
noncomputable def jointTwin (v : Fin 5 → Matrix Four Four ℂ) : Fin 5 → Matrix Four Four ℂ :=
  fun s => (-1 : ℂ) • jointSinglet v s

/-- On `a ⊗ B_k` the joint walk at the singlet's counterpart `{n}` is the counterpart's walk `K_{T_k^c} = −K_{T_k}`. -/
theorem jointTwin_channel (k : Fin 16) (a : Fin 5 → ℂ) :
    jointTwin (fun t => a t • relOp k) =
      fun s => (patternK (R := ℂ) (disagreeSet k)ᶜ *ᵥ a) s • relOp k := by
  funext s
  simp only [jointTwin, jointSinglet_channel, smul_smul]
  congr 1
  rw [patternK, patternK, thetaP_compl, Matrix.neg_mul, Matrix.neg_mulVec, Pi.neg_apply]
  ring

/-- **The four types on one operator:** the sixteen channels of `𝕁` are the singlet (`0|6`) and the
fifteen meetings of `2|4` (ten symmetric states, five vector states); the sixteen channels of `−𝕁` are the six
counterparts of `1|5` (the five `{t}` and `{n}`) and the ten colour counterparts of `3|3`. Counted by the number of
lines a channel's walk divides: `𝕁` gives `0` once and `2, 4` fifteen times; `−𝕁` gives `5` once,
`1` five times and `3` ten times. -/
theorem four_kinds :
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 0).card = 1 ∧
    (Finset.univ.filter fun k : Fin 16 =>
      (disagreeSet k).card = 2 ∨ (disagreeSet k).card = 4).card = 15 ∧
    (Finset.univ.filter fun k : Fin 16 =>
      (disagreeSet k)ᶜ.card = 1 ∨ (disagreeSet k)ᶜ.card = 5).card = 6 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k)ᶜ.card = 3).card = 10 := by
  decide

/-- **The law at the four types, both bases at once:** for every `u`, the line's walk, the sixteen
meetings and (at `−u`) the sixteen counterparts give one determinant (Propositions 54, 131; `law_meetings`,
`law_twins`). -/
theorem law_both (u : ℂ) :
    (1 - u • stepOp transitionMat).det = ∏ k, (1 - u • patternK (R := ℂ) (disagreeSet k)).det ∧
      (1 + u • stepOp transitionMat).det = ∏ k, (1 - u • patternK (R := ℂ) (disagreeSet k)ᶜ).det :=
  ⟨(law_meetings u).symm, (law_twins u).symm⟩

end Comparison.JointCells.Bases

#print axioms Comparison.JointCells.Bases.PhiL_apply
#print axioms Comparison.JointCells.Bases.transition_eq_iff
#print axioms Comparison.JointCells.Bases.Phi_transition
#print axioms Comparison.JointCells.Bases.transitionK_mulVec
#print axioms Comparison.JointCells.Bases.Phi_transitionK
#print axioms Comparison.JointCells.Bases.relOpZ_gram
#print axioms Comparison.JointCells.Bases.toComplex_semiconj
#print axioms Comparison.JointCells.Bases.relOp_gram
#print axioms Comparison.JointCells.Bases.trace_PhiL
#print axioms Comparison.JointCells.Bases.PhiL_injective
#print axioms Comparison.JointCells.Bases.PhiL_bijective
#print axioms Comparison.JointCells.Bases.contBC_mulVec
#print axioms Comparison.JointCells.Bases.contBC_eq
#print axioms Comparison.JointCells.Bases.Phi80_contB
#print axioms Comparison.JointCells.Bases.Phi80_bijective
#print axioms Comparison.JointCells.Bases.jointSinglet_channel
#print axioms Comparison.JointCells.Bases.jointTwin_channel
#print axioms Comparison.JointCells.Bases.four_kinds
#print axioms Comparison.JointCells.Bases.law_both
