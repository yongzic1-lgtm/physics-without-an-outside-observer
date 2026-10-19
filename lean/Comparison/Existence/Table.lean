module

public import Comparison.Existence.Holds
public import Comparison.Existence.Gauge
public import Comparison.Elements.Divisions

/-!
# Book VIII. The six divisions completed (Propositions 40, 41, 42, 44)

**Prop. 40, the clock column.** On the real `n × n` matrices (the rotations of P1's real six at
`n = 6`), a division `D` keeps `X` when `X θ_D = θ_D X`.
* `kept_entry`: a kept rotation has no entry across the division.
* `comm_unitTurn_entry`, `central_entry`: a kept rotation that commutes with every kept unit rotation has no
  entry `(a, b)` when a third direction lies on the side of `a` and `b`.
* `clock_dividedSet`: **a nonzero entry of a central kept rotation sits on a side of exactly two
  directions**, so a division has a clock only at `2|4`. The kept and moved counts of the table are
  `Divisions.lean`'s `four_kinds` and `six_divisions`, its loop signs `Spin.lean`'s `loop_counts`.

**Prop. 41, the clock of a line.** On the four amplitudes, with `gen` the fifteen rotations:
* `gen_comm_of_disjoint`: rotations of disjoint planes commute (checked over `ℤ[i]`).
* `clock_line_kept`, `clock_line_central`, `clock_line_moved`: `iγ_h` is kept by `{h, n}`, commutes
  with every rotation `{h, n}` keeps, and is moved at `{h}`; `clock_plane_kept`, `clock_plane_central`,
  `clock_plane_moved`: the same for the plane's rotation `γ_hγ_k` at `F = {h, k}`.
* `expIγ`: `e^{iaγ_h} = cos a + i sin a γ_h`; `expIγ_add`; `expIγ_unitary`;
  `clock_turns_singlet`: `(e^{iaγ_h} ⊗ e^{iaγ_h}) Ω = cos 2a Ω + sin 2a · i ℓ_h`;
  `quarter_turn`: `e^{i(π/2)γ_h} = iγ_h`.

**Prop. 42, count and amplitude.** For a set `D` of `r` divided lines and `γ_D` the product of its
lines in order (`gammaD`):
* `gammaD_J_transpose`: `(γ_D J)ᵀ = s_r γ_D J`, `s_r = −1, −1, +1, +1, −1, −1` for `r = 0, …, 5`;
  `C_sq`: `C_D = γ_D Θ` has `C_D² = s_r`; `amplitude_symm`: `⟨C_D v, w⟩ = s_r ⟨C_D w, v⟩`:
  antisymmetric where `C² = −1` (`r = 1, 5`), symmetric where `C² = +1` (`r = 3`);
  `hermForm_hermitian`: for even `r`, `h_D = i^{r(r−1)/2} γ_D` is Hermitian.

**Prop. 44, the step at each divided set.**
* `coinAt_sq`: for every `G` with `L = 𝟏ᵀ G 𝟏 ≠ 0`, `σ = (2/L) 𝟏𝟏ᵀ G − 1` has `σ² = 1`;
  `dividedSetG`, `dividedSetL`: `L_S = 5` for `S` even and `5 − 2k` for `S` odd (`k` lines in `S`);
  `coinAt_echo`: the reflection off `S` is `2/L_S − 1`.
* `plane_departures`: from the fifty symmetric states, `200` continuations: `80` reach a vector state,
  `120` a plane, `12` each plane.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## Prop. 40: where a clock can be -/

section Clock

variable {n : ℕ}

/-- **A kept rotation has no entry across the division.** -/
theorem kept_entry (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X * thetaD D = thetaD D * X) {a b : Fin n} (hab : ¬(a ∈ D ↔ b ∈ D)) : X a b = 0 := by
  have h := congrFun (congrFun hX a) b
  simp only [thetaD, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_cases ha : a ∈ D
  · have hb : b ∉ D := fun hb => hab ⟨fun _ => hb, fun _ => ha⟩
    simp only [ha, hb, ↓reduceIte] at h
    linarith
  · have hb : b ∈ D := by
      by_contra hb
      exact hab ⟨fun h' => absurd h' ha, fun h' => absurd h' hb⟩
    simp only [ha, hb, ↓reduceIte] at h
    linarith

/-- `[X, E_bc − E_cb]` at `(a, c)` is `X_ab` when `a ∉ {b, c}`. -/
theorem comm_unitTurn_entry (X : Matrix (Fin n) (Fin n) ℝ) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (X * unitTurn b c - unitTurn b c * X) a c = X a b := by
  have e1 : ∀ j, X a j * unitTurn b c j c = if j = b then X a b else 0 := by
    intro j
    simp only [unitTurn, Matrix.of_apply]
    by_cases hj : j = b
    · subst hj
      simp [hbc]
    · simp [hj, Ne.symm hbc]
  have e2 : ∀ j, unitTurn b c a j * X j c = 0 := by
    intro j
    simp [unitTurn, hab, hac]
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [e1, e2, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero,
    sub_zero]

/-- **A central kept rotation has no entry on a side with a third direction.** -/
theorem central_entry (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (hcent : ∀ b c : Fin n, (b ∈ D ↔ c ∈ D) → X * unitTurn b c = unitTurn b c * X)
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hside : b ∈ D ↔ c ∈ D) :
    X a b = 0 := by
  rw [← comm_unitTurn_entry X hab hac hbc, hcent b c hside, sub_self, Matrix.zero_apply]

/-- **A clock sits on a side of exactly two directions:** a nonzero entry `X_ab` of a kept rotation
that commutes with every kept unit rotation has `a, b` on one side and no third direction there. -/
theorem clock_dividedSet (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (hkept : X * thetaD D = thetaD D * X)
    (hcent : ∀ b c : Fin n, (b ∈ D ↔ c ∈ D) → X * unitTurn b c = unitTurn b c * X)
    {a b : Fin n} (hab : a ≠ b) (hX : X a b ≠ 0) :
    (a ∈ D ↔ b ∈ D) ∧ ∀ c, (c ∈ D ↔ a ∈ D) → c = a ∨ c = b := by
  have hside : a ∈ D ↔ b ∈ D := by
    by_contra h
    exact hX (kept_entry D X hkept h)
  refine ⟨hside, fun c hc => ?_⟩
  by_contra hne
  push Not at hne
  exact hX (central_entry D X hcent hab (Ne.symm hne.1) (Ne.symm hne.2)
    (hside.symm.trans hc.symm))

end Clock

/-! ## Prop. 41: the clocks on the four amplitudes -/

/-- The fifteen rotations over the Gaussian integers. -/
def genZ : Fin 5 ⊕ Fin 10 → Matrix Four Four GaussianInt
  | Sum.inl s => iZ • γZ s
  | Sum.inr f => -(γZ (planeLines f).1 * γZ (planeLines f).2)

theorem genZ_map (x : Fin 5 ⊕ Fin 10) : (genZ x).map GaussianInt.toComplex = gen x := by
  rcases x with s | f
  · rw [gen_inl, genZ]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [← γZ_map s]
    simp [iZ, GaussianInt.toComplex_def']
  · have hneg : ∀ M : Matrix Four Four GaussianInt,
        (-M).map GaussianInt.toComplex = -(M.map GaussianInt.toComplex) := by
      intro M
      ext i j
      simp
    rw [gen_inr, genZ, hneg, Matrix.map_mul, γZ_map, γZ_map]

/-- Two rotations whose planes share no direction. -/
def PlaneDisjoint (x y : Fin 5 ⊕ Fin 10) : Prop :=
  (plane x).1 ≠ (plane y).1 ∧ (plane x).1 ≠ (plane y).2 ∧
    (plane x).2 ≠ (plane y).1 ∧ (plane x).2 ≠ (plane y).2

instance : DecidableRel PlaneDisjoint := fun x y => by unfold PlaneDisjoint; infer_instance

theorem genZ_comm_of_disjoint :
    ∀ x y : Fin 5 ⊕ Fin 10, PlaneDisjoint x y → genZ x * genZ y = genZ y * genZ x := by
  decide +kernel

/-- **Rotations of disjoint planes commute.** -/
theorem gen_comm_of_disjoint (x y : Fin 5 ⊕ Fin 10) (h : PlaneDisjoint x y) :
    gen x * gen y = gen y * gen x := by
  rw [← genZ_map, ← genZ_map, ← Matrix.map_mul, ← Matrix.map_mul, genZ_comm_of_disjoint x y h]

/-- The clock of a line, `iγ_h`, is kept by `{h, n}`. -/
theorem clock_line_kept : ∀ h : Fin 5, Kept {0, h.succ} (Sum.inl h) := by
  decide

theorem kept_line_cases : ∀ (h : Fin 5) (x : Fin 5 ⊕ Fin 10),
    ((plane x).1 ∈ ({0, h.succ} : Finset (Fin 6)) ↔ (plane x).2 ∈ ({0, h.succ} : Finset (Fin 6))) →
      x = Sum.inl h ∨ PlaneDisjoint (Sum.inl h) x := by
  decide +kernel

/-- **The clock of a line commutes with every rotation its division keeps.** -/
theorem clock_line_central (h : Fin 5) (x : Fin 5 ⊕ Fin 10) (hx : Kept {0, h.succ} x) :
    gen (Sum.inl h) * gen x = gen x * gen (Sum.inl h) := by
  rw [kept_iff] at hx
  rcases kept_line_cases h x hx with rfl | hd
  · rfl
  · exact gen_comm_of_disjoint _ _ hd

/-- **At `{h}` the clock of the line is moved.** -/
theorem clock_line_moved : ∀ h : Fin 5, Moved {h.succ} (Sum.inl h) := by
  decide

/-- The plane's rotation is kept by the plane's division. -/
theorem clock_plane_kept (f : Fin 10) :
    Kept {(planeLines f).1.succ, (planeLines f).2.succ} (Sum.inr f) := by
  rw [kept_iff]
  simp [plane]

theorem kept_plane_cases : ∀ (f : Fin 10) (x : Fin 5 ⊕ Fin 10),
    ((plane x).1 ∈ ({(planeLines f).1.succ, (planeLines f).2.succ} : Finset (Fin 6)) ↔
      (plane x).2 ∈ ({(planeLines f).1.succ, (planeLines f).2.succ} : Finset (Fin 6))) →
      x = Sum.inr f ∨ PlaneDisjoint (Sum.inr f) x := by
  decide +kernel

/-- **The plane's rotation commutes with every rotation the plane's division keeps.** -/
theorem clock_plane_central (f : Fin 10) (x : Fin 5 ⊕ Fin 10)
    (hx : Kept {(planeLines f).1.succ, (planeLines f).2.succ} x) :
    gen (Sum.inr f) * gen x = gen x * gen (Sum.inr f) := by
  rw [kept_iff] at hx
  rcases kept_plane_cases f x hx with rfl | hd
  · rfl
  · exact gen_comm_of_disjoint _ _ hd

/-- **At `{h}` the plane's rotation is moved.** -/
theorem clock_plane_moved (f : Fin 10) : Moved {(planeLines f).1.succ} (Sum.inr f) := by
  rw [moved_iff]
  have : (planeLines f).2 ≠ (planeLines f).1 := Ne.symm (planeLines_ne f)
  simp [plane, this]

/-- `e^{iaγ_h} = cos a + i sin a γ_h` (the series of `e^{iaγ}` with `γ² = 1`). -/
noncomputable def expIγ (a : ℝ) (h : Fin 5) : Matrix Four Four ℂ :=
  (Real.cos a : ℂ) • 1 + (I * Real.sin a) • γ h

theorem expIγ_add (a b : ℝ) (h : Fin 5) : expIγ a h * expIγ b h = expIγ (a + b) h := by
  have hI : ∀ x y : ℂ, I * x * (I * y) = -(x * y) := by
    intro x y
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold expIγ
  rw [Real.cos_add, Real.sin_add]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    γ_mul_self, smul_smul, hI]
  push_cast
  module

theorem expIγ_unitary (a : ℝ) (h : Fin 5) : expIγ a h * expIγ (-a) h = 1 := by
  rw [expIγ_add, add_neg_cancel, expIγ]
  simp

/-- **One step along the last-step direction is a quarter turn of the clock:** `e^{i(π/2)γ_h} = iγ_h`. -/
theorem quarter_turn (h : Fin 5) : expIγ (Real.pi / 2) h = I • γ h := by
  simp [expIγ]

/-- `(1 ⊗ X) Ω = (X ⊗ 1) Ω` for `X = c + d γ_h`. -/
theorem one_kron_line_singlet (c d : ℂ) (h : Fin 5) :
    ((1 : Matrix Four Four ℂ) ⊗ₖ (c • 1 + d • γ h)) *ᵥ Ω =
      ((c • 1 + d • γ h) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  simp only [Matrix.kronecker_add, Matrix.add_kronecker, Matrix.add_mulVec, Matrix.kronecker_smul,
    Matrix.smul_kronecker, Matrix.smul_mulVec, same_from_either_thing]

/-- **The clock turns the singlet toward the last-step direction:**
`(e^{iaγ_h} ⊗ e^{iaγ_h}) Ω = cos 2a · Ω + sin 2a · i ℓ_h`, `ℓ_h = (γ_h ⊗ 1) Ω`. -/
theorem clock_turns_singlet (a : ℝ) (h : Fin 5) :
    (expIγ a h ⊗ₖ expIγ a h) *ᵥ Ω =
      (Real.cos (2 * a) : ℂ) • Ω + (Real.sin (2 * a) : ℂ) • (I • ((γ h ⊗ₖ 1) *ᵥ Ω)) := by
  have e1 : expIγ a h ⊗ₖ expIγ a h =
      (expIγ a h ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ expIγ a h) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [e1, ← Matrix.mulVec_mulVec, expIγ, one_kron_line_singlet, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have e2 : ((Real.cos a : ℂ) • (1 : Matrix Four Four ℂ) + (I * Real.sin a) • γ h) *
      ((Real.cos a : ℂ) • 1 + (I * Real.sin a) • γ h) =
      (Real.cos (2 * a) : ℂ) • 1 + (I * Real.sin (2 * a)) • γ h := by
    have := expIγ_add a a h
    simp only [expIγ, two_mul] at this ⊢
    exact this
  rw [e2, Matrix.add_kronecker, Matrix.add_mulVec, Matrix.smul_kronecker, Matrix.smul_kronecker,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_kronecker_one, Matrix.one_mulVec, smul_smul,
    mul_comm I]

/-! ## Prop. 42: count and amplitude -/

/-- The product of the divided lines in increasing order, over `ℤ[i]`. -/
def gammaDZ (D : Finset (Fin 5)) : Matrix Four Four GaussianInt :=
  (((List.finRange 5).filter fun t => t ∈ D).map γZ).prod

/-- The product of the divided lines in increasing order. -/
noncomputable def gammaD (D : Finset (Fin 5)) : Matrix Four Four ℂ :=
  (((List.finRange 5).filter fun t => t ∈ D).map γ).prod

/-- The join over `ℤ[i]`. -/
def JZ : Matrix Four Four GaussianInt := (1 : Matrix (Fin 2) (Fin 2) GaussianInt) ⊗ₖ !![0, 1; -1, 0]

/-- The sign `s_r = −(−1)^{r(r−1)/2}`: `+1` for `r ≡ 2, 3 (mod 4)`, `−1` otherwise. -/
def countSign (r : ℕ) : ℤ := if r % 4 = 2 ∨ r % 4 = 3 then 1 else -1

theorem gammaDZ_map (D : Finset (Fin 5)) : (gammaDZ D).map GaussianInt.toComplex = gammaD D := by
  rw [gammaDZ, gammaD]
  generalize ((List.finRange 5).filter fun t => t ∈ D) = l
  induction l with
  | nil => simp [Matrix.map_one]
  | cons t l ih => simp [List.map_cons, List.prod_cons, Matrix.map_mul, γZ_map, ih]

theorem JZ_map : JZ.map GaussianInt.toComplex = J := by
  four_ext <;> simp [JZ, J, ε]

theorem gammaDZ_J_transpose : ∀ D : Finset (Fin 5),
    (gammaDZ D * JZ)ᵀ = (countSign D.card : GaussianInt) • (gammaDZ D * JZ) := by
  decide +kernel

theorem gammaDZ_C_sq : ∀ D : Finset (Fin 5),
    (gammaDZ D * JZ) * (gammaDZ D * JZ).map star = (countSign D.card : GaussianInt) • 1 := by
  decide +kernel

/-- **`(γ_D J)ᵀ = s_r γ_D J`.** -/
theorem map_intSmul (c : ℤ) (M : Matrix Four Four GaussianInt) :
    ((c : GaussianInt) • M).map GaussianInt.toComplex = (c : ℂ) • M.map GaussianInt.toComplex := by
  ext i j
  simp

theorem gammaD_J_eq (D : Finset (Fin 5)) :
    gammaD D * J = (gammaDZ D * JZ).map GaussianInt.toComplex := by
  rw [Matrix.map_mul, gammaDZ_map, JZ_map]

theorem gammaD_J_transpose (D : Finset (Fin 5)) :
    (gammaD D * J)ᵀ = (countSign D.card : ℂ) • (gammaD D * J) := by
  rw [gammaD_J_eq, ← Matrix.transpose_map, gammaDZ_J_transpose D, map_intSmul]

/-- The antilinear map kept by an odd division: `C_D v = γ_D Θ v = γ_D J v̄`. -/
noncomputable def Cop (D : Finset (Fin 5)) (v : Four → ℂ) : Four → ℂ := (gammaD D * J) *ᵥ star v

/-- **`C_D² = s_r`.** -/
theorem C_sq (D : Finset (Fin 5)) (v : Four → ℂ) :
    Cop D (Cop D v) = (countSign D.card : ℂ) • v := by
  have h := congrArg (fun M => Matrix.map M GaussianInt.toComplex) (gammaDZ_C_sq D)
  have hstar : ((gammaDZ D * JZ).map star).map GaussianInt.toComplex =
      (gammaD D * J).map star := by
    rw [gammaD_J_eq]
    ext i j
    simp only [Matrix.map_apply, GaussianInt.toComplex_star]
    rfl
  simp only [Matrix.map_mul (f := GaussianInt.toComplex), hstar, map_intSmul] at h
  rw [← Matrix.map_mul, ← gammaD_J_eq] at h
  rw [Cop, Cop, star_mulVec', star_star, Matrix.mulVec_mulVec, h]
  have : (1 : Matrix Four Four GaussianInt).map GaussianInt.toComplex = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The reading of an odd division is bilinear and (anti)symmetric:**
`⟨C_D v, w⟩ = s_r ⟨C_D w, v⟩`. -/
theorem amplitude_symm (D : Finset (Fin 5)) (v w : Four → ℂ) :
    star (Cop D v) ⬝ᵥ w = (countSign D.card : ℂ) * (star (Cop D w) ⬝ᵥ v) := by
  set M := gammaD D * J with hM
  have hT : Mᵀ = (countSign D.card : ℂ) • M := gammaD_J_transpose D
  have hT' : (M.map star)ᵀ = (countSign D.card : ℂ) • M.map star := by
    rw [← Matrix.transpose_map, hT]
    ext i j
    simp
  have hs : (countSign D.card : ℂ) * countSign D.card = 1 := by
    unfold countSign
    split_ifs <;> norm_num
  have e : ∀ x : Four → ℂ, star (Cop D x) = M.map star *ᵥ x := by
    intro x
    rw [Cop, ← hM, star_mulVec', star_star]
  rw [e, e]
  calc (M.map star *ᵥ v) ⬝ᵥ w
      = (countSign D.card : ℂ) * ((countSign D.card : ℂ) * ((M.map star *ᵥ v) ⬝ᵥ w)) := by
        rw [← mul_assoc, hs, one_mul]
    _ = (countSign D.card : ℂ) * ((M.map star *ᵥ w) ⬝ᵥ v) := by
        congr 1
        rw [dotProduct_comm (M.map star *ᵥ w) v, Matrix.dotProduct_mulVec,
          ← Matrix.mulVec_transpose, hT', Matrix.smul_mulVec, smul_dotProduct, smul_eq_mul]

/-- The Hermitian form kept by an even division: `h_D = i^{r(r−1)/2} γ_D`. -/
noncomputable def hermForm (D : Finset (Fin 5)) : Matrix Four Four ℂ :=
  (I ^ (D.card * (D.card - 1) / 2)) • gammaD D

theorem hermFormZ : ∀ D : Finset (Fin 5), D.card % 2 = 0 →
    ((iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D)ᴴ =
      (iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D := by
  decide +kernel

/-- **An even division reads a state as a count:** `h_D` is Hermitian, so `⟨v, h_D v⟩` is real. -/
theorem hermForm_hermitian (D : Finset (Fin 5)) (hD : D.card % 2 = 0) :
    (hermForm D)ᴴ = hermForm D := by
  have h : (((iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D)ᴴ).map GaussianInt.toComplex =
      ((iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D).map GaussianInt.toComplex := by
    rw [hermFormZ D hD]
  have e : ((iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D).map GaussianInt.toComplex =
      hermForm D := by
    rw [hermForm, ← gammaDZ_map]
    ext i j
    simp [iZ, GaussianInt.toComplex_def']
  have hsemi : Function.Semiconj GaussianInt.toComplex star star := by
    intro a
    rw [GaussianInt.toComplex_star]
    rfl
  rw [Matrix.conjTranspose_map _ hsemi, e] at h
  exact h

/-! ## Prop. 44: the coin read at a divided set -/

section CoinAt

variable {K : Type*} [Field K]

/-- The all-ones matrix `𝟙𝟙ᵀ`. -/
def onesK : Matrix (Fin 5) (Fin 5) K := Matrix.of fun _ _ => 1

/-- **The coin read in the square `G`:** `σ_G = (2/L) 𝟙𝟙ᵀ G − 1`, `L = 𝟙ᵀ G 𝟙`. -/
def coinAt (G : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 5) (Fin 5) K :=
  (2 / ∑ i, ∑ j, G i j) • (onesK * G) - 1

theorem onesK_G_sq (G : Matrix (Fin 5) (Fin 5) K) :
    (onesK * G) * (onesK * G) = (∑ i, ∑ j, G i j) • (onesK * G) := by
  ext i j
  simp only [Matrix.mul_apply, onesK, Matrix.of_apply, one_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

/-- **The coin read at any divided set is an involution:** `σ_G² = 1` whenever `L ≠ 0`. -/
theorem coinAt_sq (G : Matrix (Fin 5) (Fin 5) K) (hL : ∑ i, ∑ j, G i j ≠ 0) :
    coinAt G * coinAt G = 1 := by
  simp only [coinAt, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, onesK_G_sq, smul_smul]
  have : 2 / (∑ i, ∑ j, G i j) * ((2 / ∑ i, ∑ j, G i j) * (∑ i, ∑ j, G i j)) =
      2 * (2 / ∑ i, ∑ j, G i j) := by
    field_simp
  rw [this]
  module

/-- The square that a divided set reads on the five directions: `1` on every line for an even divided set,
`−1` on its `k` lines for an odd one. -/
def dividedSetG (S : Finset (Fin 5)) (odd : Bool) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.diagonal fun t => if odd ∧ t ∈ S then -1 else 1

theorem dividedSetL (S : Finset (Fin 5)) (odd : Bool) :
    ∑ i, ∑ j, (dividedSetG S odd : Matrix (Fin 5) (Fin 5) K) i j =
      if odd then 5 - 2 * (S.card : K) else 5 := by
  simp only [dividedSetG, Matrix.diagonal_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  cases odd
  · simp
  · simp only [true_and, ↓reduceIte]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
    have h : (Finset.univ.filter fun t : Fin 5 => t ∉ S).card = 5 - S.card := by
      rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    rw [h]
    have hS : S.card ≤ 5 := by simpa using Finset.card_le_univ S
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    rw [Nat.cast_sub hS]
    push_cast
    ring

/-- **The reflection off the divided set:** the diagonal entry of `σ` at a line outside `S` is `2/L − 1`. -/
theorem coinAt_echo (G : Matrix (Fin 5) (Fin 5) K) (hG : ∀ i j, i ≠ j → G i j = 0) (t : Fin 5)
    (ht : G t t = 1) : coinAt G t t = 2 / (∑ i, ∑ j, G i j) - 1 := by
  simp only [coinAt, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, onesK,
    Matrix.of_apply, one_mul, Matrix.one_apply_eq, smul_eq_mul]
  rw [Finset.sum_eq_single t (fun b _ hb => hG b t hb) (by simp), ht, mul_one]

end CoinAt

/-- **The departures from the symmetric states:** of the `200` continuations from the fifty symmetric states, `80`
reach a vector state and `120` a plane, `12` each plane. -/
theorem plane_departures :
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2).card = 200 ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧
          (disagreeSet p.2.1).card = 4).card = 80 ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧
          (disagreeSet p.2.1).card = 2).card = 120 ∧
    ∀ k : Fin 16, (disagreeSet k).card = 2 →
      ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ p.2.1 = k).card = 12 := by
  decide +kernel

end Comparison

end
