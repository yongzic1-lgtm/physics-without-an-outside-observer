module

public import Comparison.Colour.ClosedAvailableTransitions
public import Comparison.Mass.Basic

/-!
# The road to the masses: the law's critical kernel is one-dimensional

At the critical step `u = 1/4` the law's
operator `1 − B/4` on the eighty states, and the available transitions operator `1 − W` on the seventy-four states
of a last-step direction (Proposition 77), have one-dimensional kernels on both sides, spanned by the constant
vector: the critical zero is simple in the sense of the kernel. These are theorems about the finite
operators, proved by the maximum principle on the step graph.

* `harmonic_const`: on a finite set with a strongly connected neighbourhood relation, a function
  equal to the mean of its values on the neighbours is constant (the maximum principle).
* `fwdStep`, `bwdStep`, `fwd_all`, `bwd_all`: from the state `(∅, 0)` every state is reached
  within five steps forward and within five steps backward; `step_connected`: **the eighty states
  are strongly connected by the steps**.
* `stepR`: the step `B` over `ℝ`; `kernel_right`, `kernel_left`: **`B v = 4v` and `wᵀB = 4wᵀ` only
  for constant `v`, `w`**.
* `watchedR`: the walk watched on the seventy-four over `ℝ`, `W = B_AA/4 + B_AD B_DA/16 +
  B_AD B_DD B_DA/64`; `watched_kernel_right`, `watched_kernel_left`: **`W v = v` and `wᵀW = wᵀ` only for
  constant `v`, `w`**: a vector the available transitions keep extends to a vector the law keeps on the eighty
  states (the available transitions are a closed level of the law), so it is constant.
-/

@[expose] public section

namespace Comparison

open Matrix

/-! ## The maximum principle -/

/-- **The maximum principle:** if every value is the mean of the values on its neighbours and the
neighbour relation connects every point to every point, the function is constant. -/
theorem harmonic_const {ι : Type*} [Finite ι] [Nonempty ι] (N : ι → Finset ι)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => b ∈ N a) a b) (v : ι → ℝ)
    (hv : ∀ i, ((N i).card : ℝ) * v i = ∑ j ∈ N i, v j) : ∀ i j, v i = v j := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max v
  have spread : ∀ a, v a = v i₀ → ∀ b ∈ N a, v b = v i₀ := by
    intro a ha b hb
    have hsum : ∑ j ∈ N a, (v i₀ - v j) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hv a, ha, sub_self]
    have hnn : ∀ j ∈ N a, 0 ≤ v i₀ - v j := fun j _ => sub_nonneg.mpr (hi₀ j)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum b hb
    linarith
  have hall : ∀ j, v j = v i₀ := by
    intro j
    induction hconn i₀ j with
    | refl => rfl
    | tail _ hbc ih => exact spread _ ih _ hbc
  intro i j
  rw [hall i, hall j]

/-! ## The eighty states are strongly connected -/

/-- One step forward: add every state that continues a state already reached. -/
def fwdStep (S : Finset State) : Finset State :=
  S ∪ Finset.univ.filter (fun t => ∃ a ∈ preds t, a ∈ S)

/-- One step backward: add every state that a state already reached continues. -/
def bwdStep (S : Finset State) : Finset State :=
  S ∪ Finset.univ.filter (fun t => ∃ a ∈ succs t, a ∈ S)

/-- **From `(∅, 0)` every state is reached within five steps forward.** -/
theorem fwd_all : fwdStep^[5] {((0 : Fin 16), (0 : Fin 5))} = Finset.univ := by
  decide +kernel

/-- **From every state `(∅, 0)` is reached within five steps.** -/
theorem bwd_all : bwdStep^[5] {((0 : Fin 16), (0 : Fin 5))} = Finset.univ := by
  decide +kernel

theorem mem_fwd (k : ℕ) (t : State) (ht : t ∈ fwdStep^[k] {((0 : Fin 16), (0 : Fin 5))}) :
    Relation.ReflTransGen Continues ((0 : Fin 16), (0 : Fin 5)) t := by
  induction k generalizing t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at ht
    rw [ht]
  | succ k ih =>
    rw [Function.iterate_succ_apply', fwdStep, Finset.mem_union, Finset.mem_filter] at ht
    rcases ht with ht | ⟨-, a, ha, haS⟩
    · exact ih t ht
    · exact (ih a haS).tail ((mem_preds a t).mp ha)

theorem mem_bwd (k : ℕ) (t : State) (ht : t ∈ bwdStep^[k] {((0 : Fin 16), (0 : Fin 5))}) :
    Relation.ReflTransGen Continues t ((0 : Fin 16), (0 : Fin 5)) := by
  induction k generalizing t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at ht
    rw [ht]
  | succ k ih =>
    rw [Function.iterate_succ_apply', bwdStep, Finset.mem_union, Finset.mem_filter] at ht
    rcases ht with ht | ⟨-, a, ha, haS⟩
    · exact ih t ht
    · exact Relation.ReflTransGen.head ((mem_succs t a).mp ha) (ih a haS)

/-- **The eighty states are strongly connected by the steps.** -/
theorem step_connected (a b : State) : Relation.ReflTransGen Continues a b := by
  have ha := mem_bwd 5 a (by rw [bwd_all]; exact Finset.mem_univ a)
  have hb := mem_fwd 5 b (by rw [fwd_all]; exact Finset.mem_univ b)
  exact ha.trans hb

/-! ## The kernel of the law at the critical step -/

theorem rtg_mono {α : Type*} {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hrp _ _ hbc)

/-- The step `B` over `ℝ`: entry `(s', s)` is one when `s'` continues `s`. -/
noncomputable abbrev stepR : Matrix State State ℝ := stepT fun _ _ => (1 : ℝ)

/-- The states that a state continues. -/
def predSet (s' : State) : Finset State := Finset.univ.filter fun s => Continues s s'

/-- The states that continue a state. -/
def succSet (s : State) : Finset State := Finset.univ.filter fun s' => Continues s s'

theorem stepR_mulVec (v : State → ℝ) (s' : State) :
    (stepR *ᵥ v) s' = ∑ s ∈ predSet s', v s := by
  simp only [stepR, stepT, Matrix.mulVec, dotProduct, Matrix.of_apply, predSet,
    Finset.sum_filter, ite_mul, one_mul, zero_mul]

theorem stepR_vecMul (w : State → ℝ) (s : State) :
    (w ᵥ* stepR) s = ∑ s' ∈ succSet s, w s' := by
  simp only [stepR, stepT, Matrix.vecMul, dotProduct, Matrix.of_apply, succSet,
    Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem card_predSet (s' : State) : (predSet s').card = 4 := card_predecessors s'

theorem card_succSet (s : State) : (succSet s).card = 4 := card_continuations s

/-- **`B v = 4v` only for constant `v`.** -/
theorem kernel_right (v : State → ℝ) (hv : stepR *ᵥ v = (4 : ℝ) • v) :
    ∃ c : ℝ, v = c • (1 : State → ℝ) := by
  have hconn : ∀ a b, Relation.ReflTransGen (fun a b => b ∈ predSet a) a b := by
    intro a b
    have h : Relation.ReflTransGen (fun x y => Continues y x) a b :=
      Relation.ReflTransGen.swap _ _ (step_connected b a)
    exact rtg_mono (fun x y hxy => by
      simp only [predSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxy) h
  have hh : ∀ i, ((predSet i).card : ℝ) * v i = ∑ j ∈ predSet i, v j := by
    intro i
    rw [card_predSet, ← stepR_mulVec, hv]
    simp
  have hc := harmonic_const predSet hconn v hh
  refine ⟨v ((0 : Fin 16), (0 : Fin 5)), ?_⟩
  funext s
  simp [hc s ((0 : Fin 16), (0 : Fin 5))]

/-- **`wᵀB = 4wᵀ` only for constant `w`.** -/
theorem kernel_left (w : State → ℝ) (hw : w ᵥ* stepR = (4 : ℝ) • w) :
    ∃ c : ℝ, w = c • (1 : State → ℝ) := by
  have hconn : ∀ a b, Relation.ReflTransGen (fun a b => b ∈ succSet a) a b := by
    intro a b
    exact rtg_mono (fun x y hxy => by
      simp only [succSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxy) (step_connected a b)
  have hh : ∀ i, ((succSet i).card : ℝ) * w i = ∑ j ∈ succSet i, w j := by
    intro i
    rw [card_succSet, ← stepR_vecMul, hw]
    simp
  have hc := harmonic_const succSet hconn w hh
  refine ⟨w ((0 : Fin 16), (0 : Fin 5)), ?_⟩
  funext s
  simp [hc s ((0 : Fin 16), (0 : Fin 5))]

/-! ## The kernel of the available transitions at the critical step -/

section Watched

variable (h : Fin 5)

/-- The available transitions block `B_AA` over `ℝ`. -/
noncomputable abbrev bAA : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  stepR.toBlock (InAvailableTransitions h) (InAvailableTransitions h)
/-- The block `B_AD` (steps from the six closed states into the available transitions). -/
noncomputable abbrev bAD : Matrix {s // InAvailableTransitions h s} {s // ¬InAvailableTransitions h s} ℝ :=
  stepR.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s)
/-- The block `B_DA` (steps from the available transitions into the six closed states). -/
noncomputable abbrev bDA : Matrix {s // ¬InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  stepR.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)
/-- The block `B_DD`. -/
noncomputable abbrev bDD : Matrix {s // ¬InAvailableTransitions h s} {s // ¬InAvailableTransitions h s} ℝ :=
  blockDD h (fun _ _ => (1 : ℝ))

/-- **The walk watched on the available transitions, over `ℝ`.** -/
noncomputable def watchedR : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  (1 / 4 : ℝ) • bAA h + (1 / 16 : ℝ) • (bAD h * bDA h) + (1 / 64 : ℝ) • (bAD h * bDD h * bDA h)

theorem bDD_sq : bDD h * bDD h = 0 := blockDD_sq h _

theorem mulVec_split_real (M : Matrix State State ℝ) (u : State → ℝ) (i : State) :
    (M *ᵥ u) i = (∑ a : {s // InAvailableTransitions h s}, M i a * u a) +
      ∑ d : {s // ¬InAvailableTransitions h s}, M i d * u d := by
  simp only [Matrix.mulVec, dotProduct]
  exact (Fintype.sum_subtype_add_sum_subtype (InAvailableTransitions h) fun x => M i x * u x).symm

theorem vecMul_split_real (M : Matrix State State ℝ) (u : State → ℝ) (j : State) :
    (u ᵥ* M) j = (∑ a : {s // InAvailableTransitions h s}, u a * M a j) +
      ∑ d : {s // ¬InAvailableTransitions h s}, u d * M d j := by
  simp only [Matrix.vecMul, dotProduct]
  exact (Fintype.sum_subtype_add_sum_subtype (InAvailableTransitions h) fun x => u x * M x j).symm

/-- A vector on the available transitions and one on the six closed states, glued on the eighty states. -/
def glue (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ) : State → ℝ :=
  fun s => if hs : InAvailableTransitions h s then v ⟨s, hs⟩ else w ⟨s, hs⟩

theorem glue_A (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (a : {s // InAvailableTransitions h s}) : glue h v w a = v a := by
  simp [glue, a.2]

theorem glue_D (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (d : {s // ¬InAvailableTransitions h s}) : glue h v w d = w d := by
  simp [glue, d.2]

theorem stepR_glue_A (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (a : {s // InAvailableTransitions h s}) :
    (stepR *ᵥ glue h v w) a = (bAA h *ᵥ v) a + (bAD h *ᵥ w) a := by
  rw [mulVec_split_real h]
  simp only [glue_A, glue_D, Matrix.mulVec, dotProduct, toBlock_apply]

theorem stepR_glue_D (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (d : {s // ¬InAvailableTransitions h s}) :
    (stepR *ᵥ glue h v w) d = (bDA h *ᵥ v) d + (bDD h *ᵥ w) d := by
  rw [mulVec_split_real h]
  simp only [glue_A, glue_D, Matrix.mulVec, dotProduct, toBlock_apply, bDD, blockDD]

theorem glue_vecMul_A (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (a : {s // InAvailableTransitions h s}) :
    (glue h v w ᵥ* stepR) a = (v ᵥ* bAA h) a + (w ᵥ* bDA h) a := by
  rw [vecMul_split_real h]
  simp only [glue_A, glue_D, Matrix.vecMul, dotProduct, toBlock_apply]

theorem glue_vecMul_D (v : {s // InAvailableTransitions h s} → ℝ) (w : {s // ¬InAvailableTransitions h s} → ℝ)
    (d : {s // ¬InAvailableTransitions h s}) :
    (glue h v w ᵥ* stepR) d = (v ᵥ* bAD h) d + (w ᵥ* bDD h) d := by
  rw [vecMul_split_real h]
  simp only [glue_A, glue_D, Matrix.vecMul, dotProduct, toBlock_apply, bDD, blockDD]

/-- **`W v = v` only for constant `v`:** the vector extends to the six closed states by
`w = (B_DA v)/4 + (B_DD B_DA v)/16`, and the glued vector is kept by the law's `B/4`. -/
theorem watched_kernel_right (v : {s // InAvailableTransitions h s} → ℝ) (hv : watchedR h *ᵥ v = v) :
    ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ) := by
  set w : {s // ¬InAvailableTransitions h s} → ℝ :=
    (1 / 4 : ℝ) • (bDA h *ᵥ v) + (1 / 16 : ℝ) • (bDD h *ᵥ (bDA h *ᵥ v)) with hw
  have hDD : bDD h *ᵥ (bDD h *ᵥ (bDA h *ᵥ v)) = 0 := by
    rw [Matrix.mulVec_mulVec, bDD_sq, Matrix.zero_mulVec]
  have hglue : stepR *ᵥ glue h v w = (4 : ℝ) • glue h v w := by
    funext s
    by_cases hs : InAvailableTransitions h s
    · have e := stepR_glue_A h v w ⟨s, hs⟩
      simp only at e
      rw [e, Pi.smul_apply, glue_A h v w ⟨s, hs⟩]
      have hv' := congrFun hv ⟨s, hs⟩
      rw [watchedR] at hv'
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ← Matrix.mulVec_mulVec] at hv'
      rw [hw]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · have e := stepR_glue_D h v w ⟨s, hs⟩
      simp only at e
      rw [e, Pi.smul_apply, glue_D h v w ⟨s, hs⟩]
      rw [hw]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hDD, smul_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
  obtain ⟨c, hc⟩ := kernel_right (glue h v w) hglue
  refine ⟨c, funext fun a => ?_⟩
  have := congrFun hc a
  rw [glue_A] at this
  simpa using this

/-- **`wᵀW = wᵀ` only for constant `w`.** -/
theorem watched_kernel_left (v : {s // InAvailableTransitions h s} → ℝ) (hv : v ᵥ* watchedR h = v) :
    ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ) := by
  set m : {s // ¬InAvailableTransitions h s} → ℝ :=
    (1 / 4 : ℝ) • (v ᵥ* bAD h) + (1 / 16 : ℝ) • ((v ᵥ* bAD h) ᵥ* bDD h) with hm
  have hDD : (v ᵥ* bAD h) ᵥ* bDD h ᵥ* bDD h = 0 := by
    rw [Matrix.vecMul_vecMul, bDD_sq, Matrix.vecMul_zero]
  have hglue : glue h v m ᵥ* stepR = (4 : ℝ) • glue h v m := by
    funext s
    by_cases hs : InAvailableTransitions h s
    · have e := glue_vecMul_A h v m ⟨s, hs⟩
      simp only at e
      rw [e, Pi.smul_apply, glue_A h v m ⟨s, hs⟩]
      have hv' := congrFun hv ⟨s, hs⟩
      rw [watchedR] at hv'
      simp only [Matrix.vecMul_add, Matrix.vecMul_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ← Matrix.vecMul_vecMul] at hv'
      rw [hm]
      simp only [Matrix.add_vecMul, Matrix.smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · have e := glue_vecMul_D h v m ⟨s, hs⟩
      simp only at e
      rw [e, Pi.smul_apply, glue_D h v m ⟨s, hs⟩]
      rw [hm]
      simp only [Matrix.add_vecMul, Matrix.smul_vecMul, hDD, smul_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
  obtain ⟨c, hc⟩ := kernel_left (glue h v m) hglue
  refine ⟨c, funext fun a => ?_⟩
  have := congrFun hc a
  rw [glue_A] at this
  simpa using this

end Watched

end Comparison

end
