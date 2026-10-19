import Comparison.Law.Returns
import Comparison.Existence.Table

/-!
# The joint cells of the second pairing at the plane `F` (2|4) and at its colour counterpart `C` (3|3)

In the second pairing P4 breaks, a meeting holding a division, and P5 completes it by the last-step direction's
walk. The one step that exists (Proposition 37) is the step of one system along a line `s`,
`γ_s = iJ_nJ_s`: two vertical steps whose grade-keeping part is a parallel rotation. At a pattern `P` the
last-step direction's step along `s` carries two systems at once:

* **vertically**, the pattern's agreement sign `ε_s(P)` (the square `f_s² = θ_P(s)` of the square-root step
  at the pattern's division; Propositions 34, 129, 132);
* **in parallel**, the frame of one system, carried by the step: `X ↦ γ_s X γ_s` (its action on P1's
  real six is `γ_s ⊗ γ_s = θ_{T_s}`, Propositions 27, 134).

The **joint walk** at `P` does both in one step (`jointWalk`): the last-step direction arrives at `s` with `ε_s(P)`
and the step along `s` carries one system's operators. This file proves its cells at the plane
`F = {h, k}` (the lines `0, 1`) and at its colour counterpart `C` (the lines `2, 3, 4`).

**The joint formula** (`joint_step_F`, `joint_step_C`): the step carries the plane's rotation `γ_hγ_k`
back with the plane's agreement sign,
`γ_s (γ_hγ_k) γ_s = ε_s(F) γ_hγ_k = −ε_s(C) γ_hγ_k`  for every line `s`.

**Its vertical projection**, the scalar channel of the joint walk (`jointWalk_scalar`), is the last-step direction's
walk `K_P` itself: at `F` the agreement signs `(−1, −1, +1, +1, +1)` (`agr_planeF`), the full cycle
`+1 = z_F²` (`full_cycle_F`), the colour last-step direction's first return `Φ(z)/z` and the plane line's `−g₃`
(`colour_return_F`, `plane_return_F`), the meeting's factor `(1 + u)²(1 − u)(1 + 4u² − u)`
(`factor_F`); at `C` the signs `(+1, +1, −1, −1, −1)`, the full cycle `−1 = z_C²`, the colour last-step direction's
return `−Φ(z)/z` and the plane line's `g₁`, the factor `(1 + u)(1 − u)²(1 + 4u² + u)`.

**Its parallel projection**, the own-rotation channel and the frame:
* `own_plane_unique_F`, `own_plane_unique_C`: among the fifteen rotations, `(h k)` is the only one whose
  parallel return around every loop `t → s → t` equals the loop's vertical return `ε_sε_t`
  (Definition 41); the loop characters of `F` and `C` are the same, so the same rotation is selected;
* `kept_F_iff`: **the frame `F` keeps is the commutant of its own rotation** `γ_hγ_k`; `own_central_F`:
  the own rotation is central there (the clock);
* `kept_C_iff`: **the frame `C` keeps is the commutant of its amplitude form** `C_C = γ_hγ_kΘ`
  (Proposition 42's antilinear form of an odd divided set; `γ_{c₁}γ_{c₂}γ_{c₃} = −γ_hγ_k`), so the line
  clocks `iγ_h`, `iγ_k` are kept at `C` although they anticommute with `γ_hγ_k`:
  `own_not_central_C`, the own rotation is kept and not central;
* `jointWalk_own_F`, `jointWalk_own_C`: on the own rotation the joint walk is the free last-step direction `K_∅` at `F`
  and `−K_∅ = K_{all five}` at `C`; its factor is `(1 + u)⁴(1 − 4u)` at `F`, the long-range zero at
  `u = 1/4`, and `(1 − u)⁴(1 + 4u)` at `C`, the zero at `u = −1/4`, the plane's own phase
  (`own_factor_F`, `own_factor_C`). This is a channel of the joint walk; it does not move the zero of
  the bare scalar factor of the plane.

`joint_cell_F` and `joint_cell_C` state each cell's formula with its two projections at once.
-/

open Comparison Matrix Kronecker
open Comparison.Law

namespace Comparison.JointCells

/-! ## The patterns, the agreement sign and the plane's rotation -/

/-- The plane `F = {h, k}`: the lines `0` and `1`. -/
def planeF : Finset (Fin 5) := {0, 1}

/-- Its colour counterpart `C`: the three lines `2, 3, 4` outside the plane. -/
def colourC : Finset (Fin 5) := {2, 3, 4}

/-- The agreement sign over `ℤ`: `−1` on the lines where the two systems disagree. -/
def agrZ (P : Finset (Fin 5)) (s : Fin 5) : ℤ := if s ∈ P then -1 else 1

/-- The agreement sign `ε_s(P)`. -/
def agr (P : Finset (Fin 5)) (s : Fin 5) : ℂ := (agrZ P s : ℂ)

theorem agr_eq (P : Finset (Fin 5)) (s : Fin 5) : agr P s = if s ∈ P then -1 else 1 := by
  unfold agr agrZ
  split_ifs <;> simp

theorem agr_mul_self (P : Finset (Fin 5)) (s : Fin 5) : agr P s * agr P s = 1 := by
  rw [agr_eq]
  split_ifs <;> norm_num

/-- The two patterns are counterparts: `ε_s(C) = −ε_s(F)` on every line. -/
theorem agr_colourC (s : Fin 5) : agr colourC s = -agr planeF s := by
  rw [agr_eq, agr_eq]
  fin_cases s <;> simp [colourC, planeF]

/-- The plane's rotation `γ_hγ_k` (the rotation `gen (inr 0)` up to its sign). -/
def planeTurn : Matrix Four Four ℂ := γ 0 * γ 1

theorem gen_inr_zero : gen (Sum.inr 0) = -planeTurn := by
  rw [gen_inr]
  rfl

/-! ## The joint formula: the step carries the own rotation with the agreement sign -/

/-- **The joint step at `F`:** `γ_s (γ_hγ_k) γ_s = ε_s(F) γ_hγ_k` for every line `s`. -/
theorem joint_step_F (s : Fin 5) : γ s * planeTurn * γ s = agr planeF s • planeTurn := by
  have h := γ_conj_relOp s 6
  have e1 : relOp 6 = planeTurn := rfl
  have e2 : disagreeSet 6 = planeF := rfl
  rw [e1, e2] at h
  rw [h, agr_eq]

/-- **The joint step at `C`:** `γ_s (γ_hγ_k) γ_s = −ε_s(C) γ_hγ_k`: the same transport, the counterpart's
agreement sign reversed (`z_C² = −1`). -/
theorem joint_step_C (s : Fin 5) : γ s * planeTurn * γ s = (-agr colourC s) • planeTurn := by
  rw [agr_colourC, neg_neg]
  exact joint_step_F s

/-- Around a loop `t → s → t` an operator carried with the signs `c` comes back with `c_s c_t`. -/
theorem loop_return (X : Matrix Four Four ℂ) (c : Fin 5 → ℂ)
    (hc : ∀ s, γ s * X * γ s = c s • X) (s t : Fin 5) :
    γ t * γ s * X * γ s * γ t = (c s * c t) • X := by
  calc γ t * γ s * X * γ s * γ t = γ t * (γ s * X * γ s) * γ t := by
        simp only [Matrix.mul_assoc]
    _ = γ t * (c s • X) * γ t := by rw [hc s]
    _ = c s • (γ t * X * γ t) := by rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c s • (c t • X) := by rw [hc t]
    _ = (c s * c t) • X := by rw [smul_smul]

/-- **Definition 41 at `F`:** the plane's rotation comes back around every loop with the loop's vertical
return `ε_s(F)ε_t(F)`. -/
theorem own_loop_F (s t : Fin 5) :
    γ t * γ s * planeTurn * γ s * γ t = (agr planeF s * agr planeF t) • planeTurn :=
  loop_return planeTurn _ joint_step_F s t

/-- **Definition 41 at `C`:** the same rotation comes back with `ε_s(C)ε_t(C)`. -/
theorem own_loop_C (s t : Fin 5) :
    γ t * γ s * planeTurn * γ s * γ t = (agr colourC s * agr colourC t) • planeTurn := by
  rw [loop_return planeTurn _ joint_step_C s t]
  congr 1
  ring

/-! ## The fifteen rotations carried by one step -/

/-- The sign by which the step along `s` carries the rotation `x`: the step acts on P1's real six as
`θ_{T_s}`, which keeps the singlet and `s` and reverses the other four lines. -/
def turnSign (s : Fin 5) : Fin 5 ⊕ Fin 10 → ℤ
  | Sum.inl u => if s = u then 1 else -1
  | Sum.inr f => if s = (planeLines f).1 ∨ s = (planeLines f).2 then -1 else 1

/-- **The step carries every rotation by a sign:** `γ_s X γ_s = ±X` for each of the fifteen rotations. -/
theorem step_gen (s : Fin 5) (x : Fin 5 ⊕ Fin 10) :
    γ s * gen x * γ s = (turnSign s x : ℂ) • gen x := by
  rcases x with u | f
  · rw [gen_inl]
    simp only [turnSign]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    by_cases h : s = u
    · subst h
      rw [γ_mul_self, Matrix.one_mul]
      simp
    · rw [γ_conj_line_ne h]
      simp [h]
  · rw [gen_inr]
    simp only [turnSign]
    have hab := planeLines_ne f
    rw [Matrix.mul_neg, Matrix.neg_mul]
    by_cases ha : s = (planeLines f).1
    · rw [ha, γ_conj_plane_left hab]
      simp
    · by_cases hb : s = (planeLines f).2
      · rw [hb, γ_conj_plane_right hab]
        simp
      · rw [γ_conj_plane_out ha hb]
        simp [ha, hb]

/-- Every one of the fifteen rotations squares to `−1`. -/
theorem gen_mul_self (x : Fin 5 ⊕ Fin 10) : gen x * gen x = -1 := by
  rcases x with u | f
  · rw [gen_inl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, γ_mul_self]
    simp
  · rw [gen_inr]
    have hab := planeLines_ne f
    have e : -(γ (planeLines f).1 * γ (planeLines f).2) * -(γ (planeLines f).1 * γ (planeLines f).2) =
        γ (planeLines f).1 * (γ (planeLines f).2 * γ (planeLines f).1) * γ (planeLines f).2 := by
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [e, γ_anticomm (Ne.symm hab)]
    simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]

theorem gen_ne_zero (x : Fin 5 ⊕ Fin 10) : gen x ≠ 0 := by
  intro h
  have h2 := gen_mul_self x
  rw [h, Matrix.zero_mul] at h2
  have h3 := congrFun (congrFun h2 (0, 0)) (0, 0)
  simp at h3

theorem planeTurn_mul_self : planeTurn * planeTurn = -1 := by
  have h := gen_mul_self (Sum.inr 0)
  rw [gen_inr_zero, neg_mul_neg] at h
  exact h

/-- Two complex numbers that scale a nonzero rotation alike are equal. -/
theorem smul_gen_cancel (x : Fin 5 ⊕ Fin 10) {a b : ℂ} (h : a • gen x = b • gen x) : a = b :=
  smul_left_injective ℂ (gen_ne_zero x) h

/-! ## The own rotation is selected by the loop character -/

/-- The combinatorial form of Definition 41: the rotation's two step signs around every loop equal the
pattern's vertical return. -/
def OwnAt (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : Prop :=
  ∀ s t : Fin 5, s ≠ t → turnSign s x * turnSign t x = agrZ P s * agrZ P t

instance (P : Finset (Fin 5)) : DecidablePred (OwnAt P) := fun x => by
  unfold OwnAt; infer_instance

theorem ownAt_iff (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) :
    (∀ s t : Fin 5, s ≠ t → γ t * γ s * gen x * γ s * γ t = (agr P s * agr P t) • gen x) ↔
      OwnAt P x := by
  have hloop : ∀ s t, γ t * γ s * gen x * γ s * γ t =
      ((turnSign s x : ℂ) * (turnSign t x : ℂ)) • gen x :=
    loop_return (gen x) _ (fun s => step_gen s x)
  constructor
  · intro h s t hst
    have h1 := h s t hst
    rw [hloop] at h1
    have h2 := smul_gen_cancel x h1
    unfold agr at h2
    exact_mod_cast h2
  · intro h s t hst
    rw [hloop]
    congr 1
    unfold agr
    exact_mod_cast h s t hst

theorem ownAt_planeF : ∀ x : Fin 5 ⊕ Fin 10, OwnAt planeF x ↔ x = Sum.inr 0 := by
  decide

theorem ownAt_colourC : ∀ x : Fin 5 ⊕ Fin 10, OwnAt colourC x ↔ x = Sum.inr 0 := by
  decide

/-- **The own rotation at `F` is unique:** among the fifteen rotations, `(h k)` alone comes back around every
loop with the loop's vertical return. -/
theorem own_plane_unique_F (x : Fin 5 ⊕ Fin 10) :
    (∀ s t : Fin 5, s ≠ t → γ t * γ s * gen x * γ s * γ t = (agr planeF s * agr planeF t) • gen x) ↔
      x = Sum.inr 0 := by
  rw [ownAt_iff, ownAt_planeF]

/-- **The own rotation at `C` is the same rotation:** the counterpart's loop character is the plane's. -/
theorem own_plane_unique_C (x : Fin 5 ⊕ Fin 10) :
    (∀ s t : Fin 5, s ≠ t →
        γ t * γ s * gen x * γ s * γ t = (agr colourC s * agr colourC t) • gen x) ↔
      x = Sum.inr 0 := by
  rw [ownAt_iff, ownAt_colourC]

/-! ## The frame: the commutant of the own element -/

/-- The plane's rotation over `ℤ[i]`. -/
def planeTurnZ : Matrix Four Four GaussianInt := γZ 0 * γZ 1

theorem planeTurnZ_map : planeTurnZ.map GaussianInt.toComplex = planeTurn := by
  rw [planeTurnZ, Matrix.map_mul, γZ_map, γZ_map]
  rfl

theorem map_toComplex_inj (A B : Matrix Four Four GaussianInt) :
    A.map GaussianInt.toComplex = B.map GaussianInt.toComplex ↔ A = B :=
  (Matrix.map_injective (fun _ _ h => GaussianInt.toComplex_inj.mp h)).eq_iff

theorem map_star_toComplex (A : Matrix Four Four GaussianInt) :
    (A.map star).map GaussianInt.toComplex = (A.map GaussianInt.toComplex).map star := by
  ext i j
  simp only [Matrix.map_apply]
  rw [GaussianInt.toComplex_star]
  rfl

theorem kept_F_Z : ∀ x : Fin 5 ⊕ Fin 10,
    Kept {1, 2} x ↔ genZ x * planeTurnZ = planeTurnZ * genZ x := by
  decide +kernel

theorem kept_C_Z : ∀ x : Fin 5 ⊕ Fin 10,
    Kept {3, 4, 5} x ↔ genZ x * (planeTurnZ * JZ) = (planeTurnZ * JZ) * (genZ x).map star := by
  decide +kernel

/-- **The frame `F` keeps is the commutant of its own rotation:** a rotation is kept by the plane's division
`{h, k}` of the six exactly when it commutes with `γ_hγ_k`. -/
theorem kept_F_iff (x : Fin 5 ⊕ Fin 10) : Kept {1, 2} x ↔ gen x * planeTurn = planeTurn * gen x := by
  rw [kept_F_Z x, ← genZ_map x, ← planeTurnZ_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (map_toComplex_inj _ _).symm

/-- **The own rotation is central in the frame `F` keeps: it is the clock** (Propositions 151, 152). -/
theorem own_central_F (x : Fin 5 ⊕ Fin 10) (hx : Kept {1, 2} x) :
    planeTurn * gen x = gen x * planeTurn :=
  ((kept_F_iff x).mp hx).symm

/-- **The frame `C` keeps is the commutant of its amplitude form** `C_C = γ_hγ_kΘ` (Proposition 42:
an odd divided set keeps the antilinear `γ_DΘ`, here `γ_{c₁}γ_{c₂}γ_{c₃} = −γ_hγ_k`): a rotation `X` is kept
by `C` exactly when `X (γ_hγ_k J) = (γ_hγ_k J) X̄`, that is `X C_C = C_C X` with `C_C v = γ_hγ_k J v̄`. -/
theorem kept_C_iff (x : Fin 5 ⊕ Fin 10) :
    Kept {3, 4, 5} x ↔ gen x * (planeTurn * J) = (planeTurn * J) * (gen x).map star := by
  rw [kept_C_Z x, ← genZ_map x, ← planeTurnZ_map, ← JZ_map, ← map_star_toComplex]
  simp only [← Matrix.map_mul]
  exact (map_toComplex_inj _ _).symm

/-- The step along `s` moved past a rotation: `γ_s X = ±X γ_s`. -/
theorem step_gen_comm (s : Fin 5) (x : Fin 5 ⊕ Fin 10) :
    γ s * gen x = (turnSign s x : ℂ) • (gen x * γ s) := by
  calc γ s * gen x = γ s * gen x * (γ s * γ s) := by rw [γ_mul_self, Matrix.mul_one]
    _ = (γ s * gen x * γ s) * γ s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [step_gen, Matrix.smul_mul]

/-- **The plane's rotation moved past a rotation** gives the rotation's two step signs on the plane:
`γ_hγ_k X = s_h(X) s_k(X) X γ_hγ_k`. -/
theorem planeTurn_mul_gen (x : Fin 5 ⊕ Fin 10) :
    planeTurn * gen x = ((turnSign 0 x : ℂ) * (turnSign 1 x : ℂ)) • (gen x * planeTurn) := by
  unfold planeTurn
  calc γ 0 * γ 1 * gen x = γ 0 * (γ 1 * gen x) := Matrix.mul_assoc _ _ _
    _ = γ 0 * ((turnSign 1 x : ℂ) • (gen x * γ 1)) := by rw [step_gen_comm]
    _ = (turnSign 1 x : ℂ) • ((γ 0 * gen x) * γ 1) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = (turnSign 1 x : ℂ) • (((turnSign 0 x : ℂ) • (gen x * γ 0)) * γ 1) := by
        rw [step_gen_comm]
    _ = _ := by rw [Matrix.smul_mul, smul_smul, mul_comm, Matrix.mul_assoc]

/-- A rotation times the plane's rotation is invertible. -/
theorem gen_planeTurn_ne_zero (x : Fin 5 ⊕ Fin 10) : gen x * planeTurn ≠ 0 := by
  intro h
  have h1 : (gen x * planeTurn) * (planeTurn * gen x) = 1 := by
    calc (gen x * planeTurn) * (planeTurn * gen x) = gen x * (planeTurn * planeTurn) * gen x := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [planeTurn_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
            gen_mul_self, neg_neg]
  rw [h, Matrix.zero_mul] at h1
  have h3 := congrFun (congrFun h1 (0, 0)) (0, 0)
  simp at h3

/-- **At `C` the own rotation is kept and not central:** the last-step direction's own clock `iγ_h` is kept by `C` (it
commutes with `C_C`) and anticommutes with `γ_hγ_k` (Propositions 157, 158). -/
theorem own_not_central_C :
    Kept {3, 4, 5} (Sum.inr 0) ∧ Kept {3, 4, 5} (Sum.inl 0) ∧
      planeTurn * gen (Sum.inl 0) = -(gen (Sum.inl 0) * planeTurn) ∧
      planeTurn * gen (Sum.inl 0) ≠ gen (Sum.inl 0) * planeTurn := by
  have hanti : planeTurn * gen (Sum.inl 0) = -(gen (Sum.inl 0) * planeTurn) := by
    rw [planeTurn_mul_gen]
    simp [turnSign]
  refine ⟨by decide, by decide, hanti, ?_⟩
  intro h
  rw [hanti] at h
  have h2 : (2 : ℂ) • (gen (Sum.inl 0) * planeTurn) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← neg_neg (gen (Sum.inl 0) * planeTurn)]
    rw [h, neg_add_cancel]
  exact gen_planeTurn_ne_zero (Sum.inl 0) ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- The kept counts: `7` at `F` (`C(2,2) + C(4,2)`), `6` at `C` (`C(3,2) + C(3,2)`). -/
theorem kept_counts :
    (Finset.univ.filter (Kept {1, 2})).card = 7 ∧ (Finset.univ.filter (Kept {3, 4, 5})).card = 6 := by
  constructor
  · rw [card_kept]; rfl
  · rw [card_kept]; rfl

/-! ## The vertical projection: the scalar channel -/

theorem agr_planeF_vals : (fun s => agr planeF s) = ![-1, -1, 1, 1, 1] := by
  funext s
  fin_cases s <;> simp [agr_eq, planeF]

theorem agr_colourC_vals : (fun s => agr colourC s) = ![1, 1, -1, -1, -1] := by
  funext s
  fin_cases s <;> simp [agr_eq, colourC]

/-- The agreements less the disagreements, `L − 1`: `1` at `F` (`L = 2`), `−1` at `C`. -/
theorem agr_sums : ∑ s, agr planeF s = 1 ∧ ∑ s, agr colourC s = -1 := by
  constructor
  · rw [Fin.sum_univ_five]; simp [agr_eq, planeF]
  · rw [Fin.sum_univ_five]; simp [agr_eq, colourC]

/-- **The full cycle is `z²`:** `det θ_F = +1 = z_F²` with `z_F = −1` (a count at `u = −1/4`), and
`det θ_C = −1 = z_C²` with `z_C = −i` (an amplitude at `u = −i/4`). -/
theorem full_cycles :
    (thetaP (R := ℂ) planeF).det = 1 ∧ zS (patternDividedSet planeF) = -1 ∧
      (thetaP (R := ℂ) colourC).det = -1 ∧ zS (patternDividedSet colourC) = -Complex.I := by
  have cF : planeF.card = 2 := rfl
  have cC : colourC.card = 3 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [full_cycle, cF]; norm_num
  · have : patternDividedSet planeF = {1, 2} := by decide
    rw [this, zS]
    have hc : ({1, 2} : Finset (Fin 6)).card = 2 := rfl
    rw [hc, Complex.I_sq]
  · rw [full_cycle, cC]; norm_num
  · have : patternDividedSet colourC = {3, 4, 5} := by decide
    rw [this, zS]
    have hc : ({3, 4, 5} : Finset (Fin 6)).card = 3 := rfl
    rw [hc, pow_succ, Complex.I_sq]
    ring

/-- **The meeting's factor at `F`:** `det(I − uK_F) = (1 + u)²(1 − u)(1 + 4u² − u)`. -/
theorem factor_F (u : ℂ) :
    (1 - u • patternK (R := ℂ) planeF).det = (1 + u) ^ 2 * (1 - u) * (1 + 4 * u ^ 2 - u) := by
  have hc : planeF.card = 2 := rfl
  rw [pattern_factor_cancelled planeF (by rw [hc]; norm_num) (by rw [hc]; norm_num) u, hc]
  norm_num

/-- **The counterpart's factor at `C`:** `det(I − uK_C) = (1 + u)(1 − u)²(1 + 4u² + u)`, the plane's at `−u`. -/
theorem factor_C (u : ℂ) :
    (1 - u • patternK (R := ℂ) colourC).det = (1 + u) * (1 - u) ^ 2 * (1 + 4 * u ^ 2 + u) := by
  have hc : colourC.card = 3 := rfl
  rw [pattern_factor_cancelled colourC (by rw [hc]; norm_num) (by rw [hc]; norm_num) u, hc]
  norm_num

/-- At their own phases: `135/128` at `u = −1/4` for `F`; the point factor `(3 − i)/4` at
`u = −i/4` for `C` (Propositions 150, 156). -/
theorem own_phase_values :
    (1 - (-1 / 4 : ℂ) • patternK (R := ℂ) planeF).det = 135 / 128 ∧
      1 + 4 * (-Complex.I / 4) ^ 2 + (-Complex.I / 4) = (3 - Complex.I) / 4 := by
  constructor
  · rw [factor_F]; norm_num
  · ring_nf
    rw [Complex.I_sq]
    ring

/-! ## The first returns of the last-step directions (Proposition 132 at `F` and `C`) -/

/-- The walk among four lines with the signs `e`: `I − x diag(e)(𝐉 − I)`, its determinant. -/
theorem det_four (x : ℂ) (e : Fin 4 → ℂ) :
    (1 - x • (diagonal e * (Matrix.of fun i j : Fin 4 => if i = j then (0 : ℂ) else 1))).det =
      (1 + x * e 0) * (1 + x * e 1) * (1 + x * e 2) * (1 + x * e 3) -
        x * (e 0 * ((1 + x * e 1) * (1 + x * e 2) * (1 + x * e 3)) +
          e 1 * ((1 + x * e 0) * (1 + x * e 2) * (1 + x * e 3)) +
          e 2 * ((1 + x * e 0) * (1 + x * e 1) * (1 + x * e 3)) +
          e 3 * ((1 + x * e 0) * (1 + x * e 1) * (1 + x * e 2))) := by
  simp only [det_succ_row_zero, Fin.sum_univ_succ, submatrix_apply,
    Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.zero_succAbove,
    Fin.succ_zero_eq_one, det_unique, Fin.default_eq_zero, Fin.sum_univ_zero,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, mul_apply, diagonal_apply, of_apply,
    smul_eq_mul]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- The walk among the four lines other than `t` at the pattern `P`. -/
theorem sub_walk (P : Finset (Fin 5)) (t : Fin 5) :
    (patternK (R := ℂ) P).submatrix t.succAbove t.succAbove =
      diagonal (fun i => agr P (t.succAbove i)) *
        (Matrix.of fun i j : Fin 4 => if i = j then (0 : ℂ) else 1) := by
  ext i j
  simp only [submatrix_apply, patternK_apply, diagonal_mul, of_apply, agr_eq,
    Fin.succAbove_right_inj]

/-- **The last-step direction's first return** at the pattern `P` from the line `t`: closing the other four lines
(Proposition 57, the Schur complement `det K = det K_oo (K_tt − K_to K_oo⁻¹ K_ot)` with `K_tt = 1`),
`G_{P,t}(x) = 1 − det(I − xK_P)/det(I − xK_P^{(t)})`, `K_P^{(t)}` the walk among the other four:
the sum over the walks that leave `t` and come back to it once. -/
noncomputable def lastDirectionReturn (P : Finset (Fin 5)) (t : Fin 5) (x : ℂ) : ℂ :=
  1 - (1 - x • patternK (R := ℂ) P).det /
    (1 - x • (patternK (R := ℂ) P).submatrix t.succAbove t.succAbove).det

theorem sub_det_F_colour (x : ℂ) :
    (1 - x • (patternK (R := ℂ) planeF).submatrix (Fin.succAbove 2) (Fin.succAbove 2)).det =
      (1 - x ^ 2) * (1 + 3 * x ^ 2) := by
  rw [sub_walk, det_four]
  simp [agr_eq, planeF, Fin.succAbove]
  ring

theorem sub_det_C_colour (x : ℂ) :
    (1 - x • (patternK (R := ℂ) colourC).submatrix (Fin.succAbove 2) (Fin.succAbove 2)).det =
      (1 - x ^ 2) * (1 + 3 * x ^ 2) := by
  rw [sub_walk, det_four]
  simp [agr_eq, colourC, Fin.succAbove]
  ring

theorem sub_det_F_plane (x : ℂ) :
    (1 - x • (patternK (R := ℂ) planeF).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det =
      (1 + x) ^ 2 * (1 - 2 * x + 3 * x ^ 2) := by
  rw [sub_walk, det_four]
  simp [agr_eq, planeF, Fin.succAbove]
  ring

theorem sub_det_C_plane (x : ℂ) :
    (1 - x • (patternK (R := ℂ) colourC).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det =
      (1 - x) ^ 2 * (1 + 2 * x + 3 * x ^ 2) := by
  rw [sub_walk, det_four]
  simp [agr_eq, colourC, Fin.succAbove]
  ring

/-- The closed forms in `x`: at `F` the colour last-step direction `−4x³/(1 + 3x²)`, the plane line
`−2x²(1 − 2x)/(1 − 2x + 3x²)`; at `C` the colour last-step direction `4x³/(1 + 3x²)`, the plane line
`−2x²(1 + 2x)/(1 + 2x + 3x²)`. -/
theorem lastDirectionReturn_x (x : ℂ) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) (h3 : 1 + 3 * x ^ 2 ≠ 0)
    (hF : 1 - 2 * x + 3 * x ^ 2 ≠ 0) (hC : 1 + 2 * x + 3 * x ^ 2 ≠ 0) :
    lastDirectionReturn planeF 2 x = -4 * x ^ 3 / (1 + 3 * x ^ 2) ∧
      lastDirectionReturn colourC 2 x = 4 * x ^ 3 / (1 + 3 * x ^ 2) ∧
      lastDirectionReturn planeF 0 x = -2 * x ^ 2 * (1 - 2 * x) / (1 - 2 * x + 3 * x ^ 2) ∧
      lastDirectionReturn colourC 0 x = -2 * x ^ 2 * (1 + 2 * x) / (1 + 2 * x + 3 * x ^ 2) := by
  have hmp : 1 - x ^ 2 ≠ 0 := by
    have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [this]; exact mul_ne_zero hm hp
  unfold lastDirectionReturn
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [factor_F, sub_det_F_colour]
    rw [eq_div_iff h3, sub_mul, one_mul, div_mul_eq_mul_div, sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', eq_div_iff (mul_ne_zero hmp h3)]
    ring
  · rw [factor_C, sub_det_C_colour]
    rw [eq_div_iff h3, sub_mul, one_mul, div_mul_eq_mul_div, sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', eq_div_iff (mul_ne_zero hmp h3)]
    ring
  · rw [factor_F, sub_det_F_plane]
    have hd : (1 + x) ^ 2 * (1 - 2 * x + 3 * x ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hp) hF
    rw [eq_div_iff hF, sub_mul, one_mul, div_mul_eq_mul_div, sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', eq_div_iff hd]
    ring
  · rw [factor_C, sub_det_C_plane]
    have hd : (1 - x) ^ 2 * (1 + 2 * x + 3 * x ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hm) hC
    rw [eq_div_iff hC, sub_mul, one_mul, div_mul_eq_mul_div, sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', eq_div_iff hd]
    ring

/-- **At `F` each colour last-step direction returns the signed excursion one step shorter, `Φ(z)/z`** (Proposition 149),
at `x = z/4`; **at `C` it returns `−Φ(z)/z`** (Proposition 155). -/
theorem colour_returns (z : ℂ) (hz : z ≠ 0) (h16 : 16 + 3 * z ^ 2 ≠ 0) (hm : 4 - z ≠ 0)
    (hp : 4 + z ≠ 0) (hF : 16 - 8 * z + 3 * z ^ 2 ≠ 0) (hC : 16 + 8 * z + 3 * z ^ 2 ≠ 0) :
    lastDirectionReturn planeF 2 (z / 4) = Phi z / z ∧ lastDirectionReturn colourC 2 (z / 4) = -(Phi z / z) := by
  have hm' : 1 - z / 4 ≠ 0 := by intro h; apply hm; linear_combination 4 * h
  have hp' : 1 + z / 4 ≠ 0 := by intro h; apply hp; linear_combination 4 * h
  have h3' : 1 + 3 * (z / 4) ^ 2 ≠ 0 := by intro h; apply h16; linear_combination 16 * h
  have hF' : 1 - 2 * (z / 4) + 3 * (z / 4) ^ 2 ≠ 0 := by
    intro h; apply hF; linear_combination 16 * h
  have hC' : 1 + 2 * (z / 4) + 3 * (z / 4) ^ 2 ≠ 0 := by
    intro h; apply hC; linear_combination 16 * h
  obtain ⟨e1, e2, -, -⟩ := lastDirectionReturn_x (z / 4) hm' hp' h3' hF' hC'
  have key : -4 * (z / 4) ^ 3 / (1 + 3 * (z / 4) ^ 2) = Phi z / z := by
    rw [Phi, div_div, div_eq_div_iff h3' (mul_ne_zero h16 hz)]
    ring
  have key' : 4 * (z / 4) ^ 3 / (1 + 3 * (z / 4) ^ 2) = -(Phi z / z) := by
    rw [← key]
    ring
  exact ⟨by rw [e1, key], by rw [e2, key']⟩

/-- At `F` the plane line's last-step direction returns `−g₃ = −z²(2 − z)/(16 − 8z + 3z²)` (Proposition 149); at `C`
it returns `g₁ = −z²(2 + z)/(16 + 8z + 3z²)` (Proposition 155). -/
theorem plane_returns (z : ℂ) (h16 : 16 + 3 * z ^ 2 ≠ 0) (hm : 4 - z ≠ 0)
    (hp : 4 + z ≠ 0) (hF : 16 - 8 * z + 3 * z ^ 2 ≠ 0) (hC : 16 + 8 * z + 3 * z ^ 2 ≠ 0) :
    lastDirectionReturn planeF 0 (z / 4) = -(z ^ 2 * (2 - z) / (16 - 8 * z + 3 * z ^ 2)) ∧
      lastDirectionReturn colourC 0 (z / 4) = -z ^ 2 * (2 + z) / (16 + 8 * z + 3 * z ^ 2) := by
  have hm' : 1 - z / 4 ≠ 0 := by intro h; apply hm; linear_combination 4 * h
  have hp' : 1 + z / 4 ≠ 0 := by intro h; apply hp; linear_combination 4 * h
  have h3' : 1 + 3 * (z / 4) ^ 2 ≠ 0 := by intro h; apply h16; linear_combination 16 * h
  have hF' : 1 - 2 * (z / 4) + 3 * (z / 4) ^ 2 ≠ 0 := by
    intro h; apply hF; linear_combination 16 * h
  have hC' : 1 + 2 * (z / 4) + 3 * (z / 4) ^ 2 ≠ 0 := by
    intro h; apply hC; linear_combination 16 * h
  obtain ⟨-, -, e3, e4⟩ := lastDirectionReturn_x (z / 4) hm' hp' h3' hF' hC'
  constructor
  · rw [e3, ← neg_div, div_eq_div_iff hF' hF]
    ring
  · rw [e4, div_eq_div_iff hC' hC]
    ring

/-- The colour last-step direction's returns at `z = 1` and at the cells' own phases: `−1/19` and `+1/19` at `F`
(`z = 1, −1`), `+1/19` and `i/13` at `C` (`z = 1, −i`). -/
theorem colour_return_values :
    lastDirectionReturn planeF 2 (1 / 4) = -1 / 19 ∧ lastDirectionReturn planeF 2 (-1 / 4) = 1 / 19 ∧
      lastDirectionReturn colourC 2 (1 / 4) = 1 / 19 ∧
      lastDirectionReturn colourC 2 (-Complex.I / 4) = Complex.I / 13 := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hx : ∀ x : ℂ, 1 - x ≠ 0 → 1 + x ≠ 0 → 1 + 3 * x ^ 2 ≠ 0 → 1 - 2 * x + 3 * x ^ 2 ≠ 0 →
      1 + 2 * x + 3 * x ^ 2 ≠ 0 → lastDirectionReturn planeF 2 x = -4 * x ^ 3 / (1 + 3 * x ^ 2) ∧
        lastDirectionReturn colourC 2 x = 4 * x ^ 3 / (1 + 3 * x ^ 2) :=
    fun x a b c d e => ⟨(lastDirectionReturn_x x a b c d e).1, (lastDirectionReturn_x x a b c d e).2.1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(hx (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
    norm_num
  · rw [(hx (-1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
    norm_num
  · rw [(hx (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2]
    norm_num
  · have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    have e1 : (1 : ℂ) - -Complex.I / 4 = (4 + Complex.I) / 4 := by ring
    have e2 : (1 : ℂ) + -Complex.I / 4 = (4 - Complex.I) / 4 := by ring
    have e3 : (1 : ℂ) + 3 * (-Complex.I / 4) ^ 2 = 13 / 16 := by
      rw [div_pow, neg_sq, hI2]; norm_num
    have e4 : (1 : ℂ) - 2 * (-Complex.I / 4) + 3 * (-Complex.I / 4) ^ 2 =
        (13 + 8 * Complex.I) / 16 := by
      rw [div_pow, neg_sq, hI2]; ring
    have e5 : (1 : ℂ) + 2 * (-Complex.I / 4) + 3 * (-Complex.I / 4) ^ 2 =
        (13 - 8 * Complex.I) / 16 := by
      rw [div_pow, neg_sq, hI2]; ring
    have n1 : (4 + Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have n2 : (4 - Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have n4 : (13 + 8 * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have n5 : (13 - 8 * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    rw [(hx (-Complex.I / 4) (by rw [e1]; exact div_ne_zero n1 (by norm_num))
      (by rw [e2]; exact div_ne_zero n2 (by norm_num)) (by rw [e3]; norm_num)
      (by rw [e4]; exact div_ne_zero n4 (by norm_num))
      (by rw [e5]; exact div_ne_zero n5 (by norm_num))).2, e3, div_pow, neg_pow, hI3]
    norm_num
    ring

/-! ## The joint walk: one operator, its scalar channel and its own channel -/

/-- `𝐉 − I` on the five directions. -/
def offD : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => if i = j then 0 else 1

/-- **The joint walk at the pattern `P`** on the last-step direction and one system's operators: arriving at `s` the
last-step direction carries the agreement sign `ε_s(P)` (vertical) and the step along `s` carries the operators by
`X ↦ γ_s X γ_s` (parallel); the last-step direction leaves every line `t ≠ s`. -/
noncomputable def jointWalk (P : Finset (Fin 5)) (v : Fin 5 → Matrix Four Four ℂ) :
    Fin 5 → Matrix Four Four ℂ :=
  fun s => agr P s • (γ s * (∑ t, (if s = t then (0 : ℂ) else 1) • v t) * γ s)

/-- **A channel of the joint walk:** an operator `X` that every step carries by a sign `c_s` is a
channel on which the joint walk is the five-line matrix `diag(ε(P) c)(𝐉 − I)`. -/
theorem jointWalk_channel (P : Finset (Fin 5)) (X : Matrix Four Four ℂ) (c : Fin 5 → ℂ)
    (hc : ∀ s, γ s * X * γ s = c s • X) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • X) =
      fun s => ((diagonal (fun s => agr P s * c s) * offD) *ᵥ a) s • X := by
  funext s
  simp only [jointWalk]
  have hsum : (∑ t, (if s = t then (0 : ℂ) else 1) • (a t • X)) =
      (∑ t, (if s = t then (0 : ℂ) else 1) * a t) • X := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
  rw [hsum, Matrix.mul_smul, Matrix.smul_mul, hc s, smul_smul, smul_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, diagonal_mul, offD, of_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The pattern's walk is the diagonal of its signs times `𝐉 − I`. -/
theorem patternK_eq (P : Finset (Fin 5)) :
    patternK (R := ℂ) P = diagonal (fun s => agr P s) * offD := by
  ext i j
  simp [patternK_apply, diagonal_mul, offD, agr_eq]

/-- **The vertical projection:** on the scalar channel the joint walk is the last-step direction's walk `K_P`. -/
theorem jointWalk_scalar (P : Finset (Fin 5)) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => (patternK (R := ℂ) P *ᵥ a) s • (1 : Matrix Four Four ℂ) := by
  rw [jointWalk_channel P 1 (fun _ => 1) (fun s => by rw [Matrix.mul_one, γ_mul_self, one_smul])]
  simp only [mul_one]
  rw [patternK_eq]

/-- **The own channel at `F`:** on the plane's rotation the joint walk is the free last-step direction `K_∅`. -/
theorem jointWalk_own_F (a : Fin 5 → ℂ) :
    jointWalk planeF (fun t => a t • planeTurn) =
      fun s => (patternK (R := ℂ) ∅ *ᵥ a) s • planeTurn := by
  rw [jointWalk_channel planeF planeTurn (agr planeF) joint_step_F]
  simp only [agr_mul_self]
  have h : (fun s => agr (∅ : Finset (Fin 5)) s) = fun _ => 1 := by
    funext s
    simp [agr_eq]
  rw [patternK_eq, h]

/-- **The own channel at `C`:** on the plane's rotation the joint walk is `−K_∅ = K_{all five}`. -/
theorem jointWalk_own_C (a : Fin 5 → ℂ) :
    jointWalk colourC (fun t => a t • planeTurn) =
      fun s => (patternK (R := ℂ) Finset.univ *ᵥ a) s • planeTurn := by
  rw [jointWalk_channel colourC planeTurn (fun s => -agr colourC s) joint_step_C]
  have h : (fun s => agr colourC s * -agr colourC s) = fun s => agr Finset.univ s := by
    funext s
    rw [mul_neg, agr_mul_self, agr_eq]
    simp
  rw [h, patternK_eq]

/-- **The own channel carries the long-range zero:** at `F` its factor is `(1 + u)⁴(1 − 4u)`, zero at
`u = 1/4`; at `C` it is `(1 − u)⁴(1 + 4u)`, zero at `u = −1/4`, the plane's own phase. -/
theorem own_factors (u : ℂ) :
    (1 - u • patternK (R := ℂ) ∅).det = (1 + u) ^ 4 * (1 - 4 * u) ∧
      (1 - u • patternK (R := ℂ) Finset.univ).det = (1 - u) ^ 4 * (1 + 4 * u) :=
  ⟨singlet_factor u, all_factor u⟩

/-- The sixteen channels: the step carries every two-spinor state's operator by its agreement sign
(`γ_conj_relOp`), so on the channel `B_k` the joint walk at `P` is `diag(ε(P) ε(T_k))(𝐉 − I)`, the
last-step direction's walk at the pattern `P △ T_k` (the operator form of character shift). -/
theorem jointWalk_relOp (P : Finset (Fin 5)) (k : Fin 16) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • relOp k) =
      fun s => (patternK (R := ℂ) (symmDiff P (disagreeSet k)) *ᵥ a) s • relOp k := by
  rw [jointWalk_channel P (relOp k) (agr (disagreeSet k))
    (fun s => by rw [γ_conj_relOp, agr_eq])]
  have h : (fun s => agr P s * agr (disagreeSet k) s) =
      fun s => agr (symmDiff P (disagreeSet k)) s := by
    funext s
    simp only [agr_eq]
    by_cases h1 : s ∈ P <;> by_cases h2 : s ∈ disagreeSet k <;> simp [h1, h2, Finset.mem_symmDiff]
  rw [h, patternK_eq]

/-! ## The two joint cells -/

/-- **The joint cell of the second pairing at the plane `F` (2|4).** One formula, the step carrying
the plane's rotation with the plane's agreement sign; its vertical projection (the scalar channel, the
last-step direction's walk `K_F`, its signs, full cycle, colour-last-step direction return and factor) and its parallel projection
(the own rotation selected by the loop character, the frame as its commutant with the own rotation central,
the own channel the free last-step direction with the long-range zero). -/
theorem joint_cell_F :
    -- the joint formula
    (∀ s, γ s * planeTurn * γ s = agr planeF s • planeTurn) ∧
    -- vertical: the scalar channel is K_F, its signs, cycle and factor
    (∀ a, jointWalk planeF (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => (patternK (R := ℂ) planeF *ᵥ a) s • (1 : Matrix Four Four ℂ)) ∧
    (fun s => agr planeF s) = ![-1, -1, 1, 1, 1] ∧ (thetaP (R := ℂ) planeF).det = 1 ∧
    (∀ z : ℂ, z ≠ 0 → 16 + 3 * z ^ 2 ≠ 0 → 4 - z ≠ 0 → 4 + z ≠ 0 → 16 - 8 * z + 3 * z ^ 2 ≠ 0 →
      16 + 8 * z + 3 * z ^ 2 ≠ 0 → lastDirectionReturn planeF 2 (z / 4) = Phi z / z) ∧
    (∀ u : ℂ, (1 - u • patternK (R := ℂ) planeF).det = (1 + u) ^ 2 * (1 - u) * (1 + 4 * u ^ 2 - u)) ∧
    -- parallel: the own rotation, the frame, the own channel
    (∀ x, (∀ s t : Fin 5, s ≠ t →
        γ t * γ s * gen x * γ s * γ t = (agr planeF s * agr planeF t) • gen x) ↔ x = Sum.inr 0) ∧
    (∀ x, Kept {1, 2} x ↔ gen x * planeTurn = planeTurn * gen x) ∧
    (∀ a, jointWalk planeF (fun t => a t • planeTurn) =
      fun s => (patternK (R := ℂ) ∅ *ᵥ a) s • planeTurn) ∧
    (∀ u : ℂ, (1 - u • patternK (R := ℂ) ∅).det = (1 + u) ^ 4 * (1 - 4 * u)) :=
  ⟨joint_step_F, jointWalk_scalar planeF, agr_planeF_vals, full_cycles.1,
    fun z hz h16 hm hp hF hC => (colour_returns z hz h16 hm hp hF hC).1, factor_F, own_plane_unique_F, kept_F_iff,
    jointWalk_own_F, singlet_factor⟩

/-- **The joint cell of the second pairing at the colour counterpart `C` (3|3).** The same transport of the
plane's rotation with the counterpart's agreement sign reversed; vertical: `K_C`, its signs, full cycle `−1`,
colour-last-step direction return `−Φ(z)/z`, factor; parallel: the same own rotation, the frame as the commutant of the
amplitude form `γ_hγ_kΘ` with the own rotation kept and not central, the own channel `K_{all five}`. -/
theorem joint_cell_C :
    (∀ s, γ s * planeTurn * γ s = (-agr colourC s) • planeTurn) ∧
    (∀ a, jointWalk colourC (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => (patternK (R := ℂ) colourC *ᵥ a) s • (1 : Matrix Four Four ℂ)) ∧
    (fun s => agr colourC s) = ![1, 1, -1, -1, -1] ∧ (thetaP (R := ℂ) colourC).det = -1 ∧
    (∀ z : ℂ, z ≠ 0 → 16 + 3 * z ^ 2 ≠ 0 → 4 - z ≠ 0 → 4 + z ≠ 0 → 16 - 8 * z + 3 * z ^ 2 ≠ 0 →
      16 + 8 * z + 3 * z ^ 2 ≠ 0 → lastDirectionReturn colourC 2 (z / 4) = -(Phi z / z)) ∧
    (∀ u : ℂ, (1 - u • patternK (R := ℂ) colourC).det = (1 + u) * (1 - u) ^ 2 * (1 + 4 * u ^ 2 + u)) ∧
    (∀ x, (∀ s t : Fin 5, s ≠ t →
        γ t * γ s * gen x * γ s * γ t = (agr colourC s * agr colourC t) • gen x) ↔ x = Sum.inr 0) ∧
    (∀ x, Kept {3, 4, 5} x ↔ gen x * (planeTurn * J) = (planeTurn * J) * (gen x).map star) ∧
    (Kept {3, 4, 5} (Sum.inl 0) ∧ planeTurn * gen (Sum.inl 0) ≠ gen (Sum.inl 0) * planeTurn) ∧
    (∀ a, jointWalk colourC (fun t => a t • planeTurn) =
      fun s => (patternK (R := ℂ) Finset.univ *ᵥ a) s • planeTurn) ∧
    (∀ u : ℂ, (1 - u • patternK (R := ℂ) Finset.univ).det = (1 - u) ^ 4 * (1 + 4 * u)) :=
  ⟨joint_step_C, jointWalk_scalar colourC, agr_colourC_vals, full_cycles.2.2.1,
    fun z hz h16 hm hp hF hC => (colour_returns z hz h16 hm hp hF hC).2, factor_C, own_plane_unique_C, kept_C_iff,
    ⟨own_not_central_C.2.1, own_not_central_C.2.2.2⟩, jointWalk_own_C, all_factor⟩

end Comparison.JointCells

#print axioms Comparison.JointCells.agr_mul_self
#print axioms Comparison.JointCells.agr_colourC
#print axioms Comparison.JointCells.gen_inr_zero
#print axioms Comparison.JointCells.joint_step_F
#print axioms Comparison.JointCells.joint_step_C
#print axioms Comparison.JointCells.loop_return
#print axioms Comparison.JointCells.own_loop_F
#print axioms Comparison.JointCells.own_loop_C
#print axioms Comparison.JointCells.step_gen
#print axioms Comparison.JointCells.gen_mul_self
#print axioms Comparison.JointCells.gen_ne_zero
#print axioms Comparison.JointCells.planeTurn_mul_self
#print axioms Comparison.JointCells.ownAt_iff
#print axioms Comparison.JointCells.ownAt_planeF
#print axioms Comparison.JointCells.ownAt_colourC
#print axioms Comparison.JointCells.own_plane_unique_F
#print axioms Comparison.JointCells.own_plane_unique_C
#print axioms Comparison.JointCells.kept_F_Z
#print axioms Comparison.JointCells.kept_C_Z
#print axioms Comparison.JointCells.kept_F_iff
#print axioms Comparison.JointCells.own_central_F
#print axioms Comparison.JointCells.kept_C_iff
#print axioms Comparison.JointCells.step_gen_comm
#print axioms Comparison.JointCells.planeTurn_mul_gen
#print axioms Comparison.JointCells.gen_planeTurn_ne_zero
#print axioms Comparison.JointCells.own_not_central_C
#print axioms Comparison.JointCells.kept_counts
#print axioms Comparison.JointCells.agr_planeF_vals
#print axioms Comparison.JointCells.agr_colourC_vals
#print axioms Comparison.JointCells.agr_sums
#print axioms Comparison.JointCells.full_cycles
#print axioms Comparison.JointCells.factor_F
#print axioms Comparison.JointCells.factor_C
#print axioms Comparison.JointCells.own_phase_values
#print axioms Comparison.JointCells.det_four
#print axioms Comparison.JointCells.sub_walk
#print axioms Comparison.JointCells.sub_det_F_colour
#print axioms Comparison.JointCells.sub_det_C_colour
#print axioms Comparison.JointCells.sub_det_F_plane
#print axioms Comparison.JointCells.sub_det_C_plane
#print axioms Comparison.JointCells.lastDirectionReturn_x
#print axioms Comparison.JointCells.colour_returns
#print axioms Comparison.JointCells.plane_returns
#print axioms Comparison.JointCells.colour_return_values
#print axioms Comparison.JointCells.jointWalk_channel
#print axioms Comparison.JointCells.patternK_eq
#print axioms Comparison.JointCells.jointWalk_scalar
#print axioms Comparison.JointCells.jointWalk_own_F
#print axioms Comparison.JointCells.jointWalk_own_C
#print axioms Comparison.JointCells.own_factors
#print axioms Comparison.JointCells.jointWalk_relOp
#print axioms Comparison.JointCells.joint_cell_F
#print axioms Comparison.JointCells.joint_cell_C
#print axioms Comparison.JointCells.agr_eq
#print axioms Comparison.JointCells.planeTurnZ_map
#print axioms Comparison.JointCells.map_star_toComplex
#print axioms Comparison.JointCells.map_toComplex_inj
#print axioms Comparison.JointCells.smul_gen_cancel
