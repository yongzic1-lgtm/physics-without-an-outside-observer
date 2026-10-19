import Comparison.System.Geometry.SixDirections
import Comparison.GroupsContinuumLaw.Planes
import Comparison.GroupsContinuumLaw.Cone
import Comparison.Existence.Holds
import Comparison.Existence.Table

/-!
# The geometry of comparison, Book IV: divisions (Propositions 21 and 22, and the Lemma)

* `lemma_division_even`, `lemma_division_odd` (**the Lemma: what a division keeps on `H`**): for every
  set `D` of the five directions, divided with the singlet undivided, the fifteen generators of its real form
  (the kept rotations and `i` times the moved ones) keep on `H` the form `h_D = i^{r(r−1)/2}γ_D`
  (`X†h + hX = 0`) when `r = |D|` is even, and commute with the antilinear `C_D = γ_DΘ` when `r` is odd;
  `h_D` is Hermitian with `h_D² = 1` and, for `r = 2, 4`, trace zero and two plus and two minus signs;
  `C_D² = −1` for `r = 1, 5` and `+1` for `r = 3`.
* `realGen_span_iff_even`, `realGen_span_iff_odd`: conversely, the trace-zero `X` that keep `h_D`
  (resp. commute with `C_D`) are exactly the real combinations of the fifteen generators: the real form's
  Lie algebra is `su(h_D)` (resp. the commutant of `C_D`).
* `prop_21`, `prop_22`.
-/

open scoped InnerProductSpace Kronecker ComplexOrder
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## The fifteen generators of the real form of a division of the lines -/

/-- The division of the six that divides the lines `D` with the singlet undivided. -/
def linesDiv (D : Finset (Fin 5)) : Finset (Fin 6) := D.map (Fin.succEmb 5)

/-- A rotation is kept by the division of the lines `D`. -/
def KeptLines (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : Prop := Kept (linesDiv D) x

instance (D : Finset (Fin 5)) : DecidablePred (KeptLines D) := fun x => by
  unfold KeptLines; infer_instance

/-- **The generators of the real form:** the kept rotations, and `i` times the moved rotations. -/
noncomputable def realGen (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : Matrix Four Four ℂ :=
  if KeptLines D x then gen x else Complex.I • gen x

/-- The same over the Gaussian integers. -/
def realGenZ (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : Matrix Four Four GaussianInt :=
  if KeptLines D x then genZ x else iZ • genZ x

/-- The form of an even division over the Gaussian integers. -/
def hermFormZ (D : Finset (Fin 5)) : Matrix Four Four GaussianInt :=
  (iZ ^ (D.card * (D.card - 1) / 2)) • gammaDZ D

theorem map_smul_toComplex (c : GaussianInt) (M : Matrix Four Four GaussianInt) :
    (c • M).map GaussianInt.toComplex = (GaussianInt.toComplex c) • M.map GaussianInt.toComplex := by
  ext i j
  simp

theorem toComplex_iZ' : GaussianInt.toComplex iZ = Complex.I := by
  simp [iZ, GaussianInt.toComplex_def']

theorem realGenZ_map (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) :
    (realGenZ D x).map GaussianInt.toComplex = realGen D x := by
  unfold realGenZ realGen
  split_ifs
  · exact genZ_map x
  · rw [map_smul_toComplex, genZ_map, toComplex_iZ']

theorem hermFormZ_map (D : Finset (Fin 5)) :
    (hermFormZ D).map GaussianInt.toComplex = hermForm D := by
  rw [hermFormZ, map_smul_toComplex, gammaDZ_map, hermForm]
  congr 1
  rw [map_pow, toComplex_iZ']

theorem conjTranspose_mapZ (M : Matrix Four Four GaussianInt) :
    Mᴴ.map GaussianInt.toComplex = (M.map GaussianInt.toComplex)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, GaussianInt.toComplex_star]

theorem star_mapZ (M : Matrix Four Four GaussianInt) :
    (M.map star).map GaussianInt.toComplex = (M.map GaussianInt.toComplex).map star := by
  ext i j
  simp [GaussianInt.toComplex_star]

/-! ### The Lemma over the Gaussian integers -/

theorem lemma_evenZ : ∀ D : Finset (Fin 5), ∀ x : Fin 5 ⊕ Fin 10, D.card % 2 = 0 →
    (realGenZ D x)ᴴ * hermFormZ D + hermFormZ D * realGenZ D x = 0 := by
  decide +kernel

theorem lemma_oddZ : ∀ D : Finset (Fin 5), ∀ x : Fin 5 ⊕ Fin 10, D.card % 2 = 1 →
    realGenZ D x * (gammaDZ D * JZ) = (gammaDZ D * JZ) * (realGenZ D x).map star := by
  decide +kernel

/-- Each generator commutes or anticommutes with `h_D`: commutes exactly when kept. -/
theorem gen_hermFormZ : ∀ D : Finset (Fin 5), ∀ x : Fin 5 ⊕ Fin 10, D.card % 2 = 0 →
    (KeptLines D x → genZ x * hermFormZ D = hermFormZ D * genZ x) ∧
    (¬ KeptLines D x → genZ x * hermFormZ D = -(hermFormZ D * genZ x)) := by
  decide +kernel

/-- Each generator commutes or anticommutes with `C_D`: commutes exactly when kept. -/
theorem gen_CZ : ∀ D : Finset (Fin 5), ∀ x : Fin 5 ⊕ Fin 10, D.card % 2 = 1 →
    (KeptLines D x → genZ x * (gammaDZ D * JZ) = (gammaDZ D * JZ) * (genZ x).map star) ∧
    (¬ KeptLines D x → genZ x * (gammaDZ D * JZ) = -((gammaDZ D * JZ) * (genZ x).map star)) := by
  decide +kernel

theorem hermFormZ_sq : ∀ D : Finset (Fin 5), D.card % 2 = 0 → hermFormZ D * hermFormZ D = 1 := by
  decide +kernel

theorem hermFormZ_trace : ∀ D : Finset (Fin 5), D.card % 2 = 0 → D.card ≠ 0 →
    (hermFormZ D).trace = 0 := by
  decide +kernel

/-! ### The Lemma over the complex numbers -/

/-- **The Lemma, even divisions:** every generator of the real form keeps the form `h_D`. -/
theorem lemma_division_even (D : Finset (Fin 5)) (hD : D.card % 2 = 0) (x : Fin 5 ⊕ Fin 10) :
    (realGen D x)ᴴ * hermForm D + hermForm D * realGen D x = 0 := by
  have h := congrArg (RingHom.mapMatrix GaussianInt.toComplex) (lemma_evenZ D x hD)
  simp only [map_add, map_mul, map_zero, RingHom.mapMatrix_apply, conjTranspose_mapZ, realGenZ_map,
    hermFormZ_map] at h
  exact h

/-- **The Lemma, odd divisions:** every generator of the real form commutes with `C_D = γ_DΘ`. -/
theorem lemma_division_odd (D : Finset (Fin 5)) (hD : D.card % 2 = 1) (x : Fin 5 ⊕ Fin 10)
    (v : Four → ℂ) : realGen D x *ᵥ Cop D v = Cop D (realGen D x *ᵥ v) := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (lemma_oddZ D x hD)
  simp only [Matrix.map_mul, star_mapZ, realGenZ_map, gammaDZ_map, JZ_map] at h
  rw [Cop, Cop, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, star_mulVec']

/-- `h_D` is Hermitian with `h_D² = 1`; for `r = 2, 4` it has trace zero. -/
theorem hermForm_props (D : Finset (Fin 5)) (hD : D.card % 2 = 0) :
    (hermForm D)ᴴ = hermForm D ∧ hermForm D * hermForm D = 1 ∧
    (D.card ≠ 0 → (hermForm D).trace = 0) := by
  refine ⟨hermForm_hermitian D hD, ?_, fun h0 => ?_⟩
  · have h := congrArg (fun M => M.map GaussianInt.toComplex) (hermFormZ_sq D hD)
    simp only [Matrix.map_mul, hermFormZ_map] at h
    simpa using h
  · have h := congrArg GaussianInt.toComplex (hermFormZ_trace D hD h0)
    rw [GroupsContinuumLaw.trace_map_toComplex, hermFormZ_map] at h
    simpa using h

/-! ## The divisions of the lines on P1's real six -/

theorem gamma_on_sixZ : ∀ S : Finset (Fin 5), S.card % 2 = 0 → ∀ c : Fin 6,
    gammaDZ S * GroupsContinuumLaw.sixZ c * (gammaDZ S)ᵀ =
      (if c ∈ linesDiv S then -1 else 1 : GaussianInt) • GroupsContinuumLaw.sixZ c := by
  decide +kernel

/-- **`γ_S ⊗ γ_S = θ_S` on P1's real six for every even set `S` of lines:** `−1` on the divided lines,
`+1` on the singlet and the other lines. -/
theorem gamma_on_six (S : Finset (Fin 5)) (hS : S.card % 2 = 0) (c : Fin 6) :
    (gammaS S ⊗ₖ gammaS S) *ᵥ relOf (sixP1 c) =
      (if c ∈ linesDiv S then -1 else 1 : ℂ) • relOf (sixP1 c) := by
  rw [kron_mulVec_relOf]
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (gamma_on_sixZ S hS c)
  simp only [Matrix.map_mul, map_smul_toComplex, gammaDZ_map, GroupsContinuumLaw.sixZ_map] at h
  rw [Matrix.transpose_map, gammaDZ_map] at h
  rw [h, relOf_smul]
  congr 1
  split_ifs <;> simp

theorem gammaDZ_univ : gammaDZ Finset.univ = 1 := by
  decide +kernel

theorem gammaDZ_erase : ∀ t : Fin 5,
    gammaDZ (Finset.univ.erase t) = γZ t ∨ gammaDZ (Finset.univ.erase t) = -γZ t := by
  decide +kernel

/-- **All five lines divided: `γ_D = 1`, so `C_D = Θ`.** -/
theorem gammaS_univ : gammaS Finset.univ = 1 := by
  rw [gammaS, ← gammaDZ_map, gammaDZ_univ]
  ext i j
  simp [Matrix.one_apply]

/-- **The four lines outside `t`: `γ_D = ±γ_t`.** -/
theorem gammaS_erase (t : Fin 5) :
    gammaS (Finset.univ.erase t) = γ t ∨ gammaS (Finset.univ.erase t) = -γ t := by
  rw [gammaS, ← gammaDZ_map, ← γZ_map]
  rcases gammaDZ_erase t with h | h
  · left; rw [h]
  · right
    rw [h]
    ext i j
    simp

theorem zero_not_mem_linesDiv (D : Finset (Fin 5)) : (0 : Fin 6) ∉ linesDiv D := by
  simp [linesDiv, Fin.succ_ne_zero]

theorem card_linesDiv (D : Finset (Fin 5)) : (linesDiv D).card = D.card := Finset.card_map _

/-- Dividing the singlet with the lines `D` is the same division as dividing the lines outside `D`. -/
theorem linesDiv_compl (D : Finset (Fin 5)) : (insert 0 (linesDiv D))ᶜ = linesDiv Dᶜ := by
  ext c
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨s, rfl⟩
  · simp [linesDiv]
  · simp [linesDiv, Fin.succ_ne_zero]

/-- **Kept and moved among the ten:** dividing `r` lines with the singlet undivided keeps
`C(r,2) + C(5−r,2)` of the ten rotations that keep the singlet and moves `r(5 − r)`. -/
theorem kept_ten_lines (D : Finset (Fin 5)) :
    (Finset.univ.filter fun f : Fin 10 => Kept (linesDiv D) (Sum.inr f)).card =
      D.card.choose 2 + (5 - D.card).choose 2 ∧
    (Finset.univ.filter fun f : Fin 10 => Moved (linesDiv D) (Sum.inr f)).card =
      D.card * (5 - D.card) := by
  have he : (linesDiv D).erase 0 = linesDiv D := Finset.erase_eq_self.mpr (zero_not_mem_linesDiv D)
  rw [card_kept_ten, card_moved_ten, he, card_linesDiv]
  exact ⟨rfl, rfl⟩

/-! ## Every division is a coordinate division turned: the four types -/

/-- Two divisions are carried one to the other by a rotation of `SU(4)` when the rotation carries the
divided part of one onto the divided or the undivided part of the other. -/
def Division.ByTurn (D D' : Division) : Prop :=
  ∃ U : GroupsContinuumLaw.SU4, D' = D.map (GroupsContinuumLaw.rot6Hom U).toLinearEquiv.toLinearMap ∨
    D'ᗮ = D.map (GroupsContinuumLaw.rot6Hom U).toLinearEquiv.toLinearMap

theorem finrank_division_le (D : Division) : finrank ℝ D ≤ 6 := by
  have h := Submodule.finrank_le D
  rwa [finrank_euclideanSpace_fin] at h

theorem finrank_orth (D : Division) : finrank ℝ Dᗮ = 6 - finrank ℝ D := by
  have h := D.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at h
  omega

/-- **Under the fifteen rotations a division is known by the dimension of its smaller part.** -/
theorem byTurn_iff_kind (D D' : Division) :
    Division.ByTurn D D' ↔ Division.kind D = Division.kind D' := by
  have hle := finrank_division_le D
  have hle' := finrank_division_le D'
  constructor
  · rintro ⟨U, h | h⟩
    · have e : finrank ℝ D' = finrank ℝ D := by
        rw [h]; exact LinearEquiv.finrank_map_eq _ _
      simp only [Division.kind, e]
    · have e : finrank ℝ D'ᗮ = finrank ℝ D := by
        rw [h]; exact LinearEquiv.finrank_map_eq _ _
      rw [finrank_orth] at e
      simp only [Division.kind, Nat.min_def]
      split_ifs <;> omega
  · intro h
    simp only [Division.kind, Nat.min_def] at h
    have h2 : finrank ℝ D = finrank ℝ D' ∨ finrank ℝ D = 6 - finrank ℝ D' := by
      split_ifs at h <;> omega
    rcases h2 with h1 | h1
    · obtain ⟨U, hU⟩ := GroupsContinuumLaw.su4_moves_planes D D' h1
      refine ⟨U, Or.inl ?_⟩
      ext x
      rw [hU x, Submodule.mem_map]
      rfl
    · obtain ⟨U, hU⟩ := GroupsContinuumLaw.su4_moves_planes D D'ᗮ (by rw [finrank_orth]; exact h1)
      refine ⟨U, Or.inr ?_⟩
      ext x
      rw [hU x, Submodule.mem_map]
      rfl

/-- The coordinate division of a set `S` has dimension `|S|`. -/
theorem finrank_ofSet (S : Finset (Fin 6)) : finrank ℝ (Division.ofSet S) = S.card := by
  have hv : LinearIndependent ℝ
      (fun a : Fin 6 => (EuclideanSpace.single a (1 : ℝ) : GroupsContinuumLaw.E6)) := by
    have := (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis.linearIndependent
    convert this using 1
    funext a
    simp
  have hD : LinearIndependent ℝ (fun x : ↥(S : Set (Fin 6)) =>
      (EuclideanSpace.single (x : Fin 6) (1 : ℝ) : GroupsContinuumLaw.E6)) := hv.comp _ Subtype.val_injective
  rw [Division.ofSet, Set.image_eq_range, finrank_span_eq_card hD]
  simp

/-- **There are four types:** every division has type `0, 1, 2` or `3`, and each type is the type of
a coordinate division. -/
theorem four_kinds_general :
    (∀ D : Division, Division.kind D ≤ 3) ∧
    (∀ k ≤ 3, ∃ S : Finset (Fin 6), S.card = k ∧ Division.kind (Division.ofSet S) = k) := by
  refine ⟨fun D => ?_, fun k hk => ?_⟩
  · have := finrank_division_le D
    simp only [Division.kind, Nat.min_def]
    split_ifs <;> omega
  · refine ⟨Finset.univ.filter fun a : Fin 6 => a.val < k, ?_, ?_⟩
    · interval_cases k <;> decide
    · have hc : (Finset.univ.filter fun a : Fin 6 => a.val < k).card = k := by
        interval_cases k <;> decide
      simp only [Division.kind, finrank_ofSet, hc, Nat.min_def]
      split_ifs <;> omega

/-- **The metric of a coordinate division:** `g_D(v) = Σ_{a ∉ D} v_a² − Σ_{a ∈ D} v_a²`,
signature `(6 − k, k)`. -/
theorem metric_ofSet (D : Finset (Fin 6)) (v : Fin 6 → ℝ) :
    metricOf (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) v =
      ((∑ a, (if a ∈ D then 0 else v a ^ 2) - ∑ a, (if a ∈ D then v a ^ 2 else 0) : ℝ) : ℂ) := by
  have hS : (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0)ᵀ =
      Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0 := Matrix.diagonal_transpose _
  have hP : (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) *
      (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) =
        Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0 := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    split_ifs <;> simp
  rw [metricOf_eq _ hS hP]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_diagonal, Pi.sub_apply]
    split_ifs <;> simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.mulVec_diagonal]
    split_ifs <;> simp

/-! ## The converse of the Lemma: the generators of the real form are all its generators -/

theorem gen_linearIndependent_complex : LinearIndependent ℂ gen := by
  have h := obs_linearIndependent.comp genIdx genIdx_injective
  have hu := h.units_smul (fun _ : Fin 5 ⊕ Fin 10 => Units.mk0 Complex.I Complex.I_ne_zero)
  convert hu using 1
  funext x
  simp [gen, Units.smul_def]

theorem gen_trace' (x : Fin 5 ⊕ Fin 10) : (gen x).trace = 0 := by
  rw [gen, Matrix.trace_smul, obs_trace, if_neg (genIdx_ne_zero x), smul_zero]

/-- The factor of a generator of the real form: `1` when kept, `i` when moved. -/
noncomputable def realFactor (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : ℂ :=
  if KeptLines D x then 1 else Complex.I

theorem realFactor_ne_zero (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : realFactor D x ≠ 0 := by
  unfold realFactor; split_ifs <;> simp

theorem realGen_eq (D : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) :
    realGen D x = realFactor D x • gen x := by
  unfold realGen realFactor; split_ifs <;> simp

theorem realGen_linearIndependent (D : Finset (Fin 5)) : LinearIndependent ℂ (realGen D) := by
  have hu := gen_linearIndependent_complex.units_smul
    (fun x => Units.mk0 (realFactor D x) (realFactor_ne_zero D x))
  convert hu using 1
  funext x
  simp [realGen_eq, Units.smul_def]

/-- Every operator of trace zero is a complex combination of the fifteen generators. -/
theorem exists_gen_coeffs (X : Matrix Four Four ℂ) (htr : X.trace = 0) :
    ∃ c : Fin 5 ⊕ Fin 10 → ℂ, X = ∑ x, c x • gen x := by
  set A : Matrix Four Four ℂ := (1 / 2 : ℂ) • (X - Xᴴ) with hA
  set B : Matrix Four Four ℂ := (-Complex.I / 2) • (X + Xᴴ) with hB
  have htrH : Xᴴ.trace = 0 := by rw [Matrix.trace_conjTranspose, htr, star_zero]
  have hAm : A ∈ su4 := by
    refine ⟨?_, ?_⟩
    · rw [hA, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      simp only [star_div₀, star_one, star_ofNat]
      rw [← neg_sub, smul_neg]
    · rw [hA, Matrix.trace_smul, Matrix.trace_sub, htr, htrH, sub_zero, smul_zero]
  have hBm : B ∈ su4 := by
    refine ⟨?_, ?_⟩
    · rw [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
      have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
        apply Complex.ext <;> norm_num
      rw [hs, neg_smul, add_comm]
    · rw [hB, Matrix.trace_smul, Matrix.trace_add, htr, htrH, add_zero, smul_zero]
  rw [su4_eq_span, Submodule.mem_span_range_iff_exists_fun] at hAm hBm
  obtain ⟨a, ha⟩ := hAm
  obtain ⟨b, hb⟩ := hBm
  refine ⟨fun x => (a x : ℂ) + Complex.I * (b x : ℂ), ?_⟩
  have hX : X = A + Complex.I • B := by
    rw [hA, hB, smul_smul]
    rw [show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]]
    rw [← smul_add, sub_add_add_cancel, ← two_smul ℂ X, smul_smul]
    norm_num
  rw [hX, ← ha, ← hb, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- A real combination of the generators of the real form, written with complex coefficients. -/
theorem realGen_real_comb (D : Finset (Fin 5)) (X : Matrix Four Four ℂ) (htr : X.trace = 0) :
    ∃ p q : Fin 5 ⊕ Fin 10 → ℝ, X = ∑ x, (p x : ℂ) • realGen D x +
      Complex.I • ∑ x, (q x : ℂ) • realGen D x := by
  obtain ⟨c, hc⟩ := exists_gen_coeffs X htr
  set w : Fin 5 ⊕ Fin 10 → ℂ := fun x => c x / realFactor D x with hw
  refine ⟨fun x => (w x).re, fun x => (w x).im, ?_⟩
  rw [hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, ← add_smul, realGen_eq, smul_smul]
  congr 1
  have hre : ((w x).re : ℂ) + Complex.I * ((w x).im : ℂ) = w x := by
    rw [mul_comm]; exact Complex.re_add_im (w x)
  rw [hre, hw]
  field_simp [realFactor_ne_zero D x]

theorem sum_real_conjTranspose (D : Finset (Fin 5)) (q : Fin 5 ⊕ Fin 10 → ℝ) :
    (∑ x, (q x : ℂ) • realGen D x)ᴴ = ∑ x, (q x : ℂ) • (realGen D x)ᴴ := by
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]

/-- **The converse of the Lemma, even divisions:** the operators of trace zero that keep the form `h_D`
(`X†h_D + h_DX = 0`) are exactly the real combinations of the fifteen generators of the real form. -/
theorem realGen_span_iff_even (D : Finset (Fin 5)) (hD : D.card % 2 = 0) (X : Matrix Four Four ℂ) :
    (X.trace = 0 ∧ Xᴴ * hermForm D + hermForm D * X = 0) ↔
      X ∈ Submodule.span ℝ (Set.range (realGen D)) := by
  have hR := fun x => lemma_division_even D hD x
  have hsum : ∀ q : Fin 5 ⊕ Fin 10 → ℝ,
      (∑ x, (q x : ℂ) • realGen D x)ᴴ * hermForm D + hermForm D * ∑ x, (q x : ℂ) • realGen D x = 0 := by
    intro q
    rw [sum_real_conjTranspose, Finset.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hR x, smul_zero]
  have htrR : ∀ x, (realGen D x).trace = 0 := by
    intro x
    rw [realGen_eq, Matrix.trace_smul]
    rw [gen_trace' x, smul_zero]
  constructor
  · rintro ⟨htr, hX⟩
    obtain ⟨p, q, hpq⟩ := realGen_real_comb D X htr
    set Y := ∑ x, (q x : ℂ) • realGen D x with hY
    set Z := ∑ x, (p x : ℂ) • realGen D x with hZ
    have hYc := hsum q
    have hZc := hsum p
    rw [← hY] at hYc
    rw [← hZ] at hZc
    have hhY : hermForm D * Y = 0 := by
      have e : Xᴴ * hermForm D + hermForm D * X = (2 * Complex.I) • (hermForm D * Y) := by
        have hYh : Yᴴ * hermForm D = -(hermForm D * Y) := eq_neg_of_add_eq_zero_left hYc
        rw [hpq, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
          Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hYh, Complex.star_def, Complex.conj_I]
        linear_combination (norm := module) hZc
      rw [e] at hX
      exact (smul_eq_zero.mp hX).resolve_left (by simp)
    have hY0 : Y = 0 := by
      have h2 := (hermForm_props D hD).2.1
      calc Y = (hermForm D * hermForm D) * Y := by rw [h2, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, hhY, Matrix.mul_zero]
    have hq : ∀ x, (q x : ℂ) = 0 := by
      have := Fintype.linearIndependent_iff.mp (realGen_linearIndependent D) (fun x => (q x : ℂ))
        (by rw [← hY]; exact hY0)
      exact this
    have hX' : X = Z := by
      rw [hpq, hY0, smul_zero, add_zero]
    rw [hX', hZ]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [Complex.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · intro hX
    rw [Submodule.mem_span_range_iff_exists_fun] at hX
    obtain ⟨p, rfl⟩ := hX
    have e : ∑ x, p x • realGen D x = ∑ x, (p x : ℂ) • realGen D x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.coe_smul]
    rw [e]
    refine ⟨?_, hsum p⟩
    rw [Matrix.trace_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.trace_smul, htrR x, smul_zero]


/-- **The converse of the Lemma, odd divisions:** the operators of trace zero that commute with the
antilinear `C_D` (`X M = M X̄`, `M = γ_DJ`) are exactly the real combinations of the fifteen
generators of the real form. -/
theorem realGen_span_iff_odd (D : Finset (Fin 5)) (hD : D.card % 2 = 1) (X : Matrix Four Four ℂ) :
    (X.trace = 0 ∧ X * (gammaD D * J) = (gammaD D * J) * X.map star) ↔
      X ∈ Submodule.span ℝ (Set.range (realGen D)) := by
  set M := gammaD D * J with hMdef
  have hRZ := fun x => lemma_oddZ D x hD
  have hR : ∀ x, realGen D x * M = M * (realGen D x).map star := by
    intro x
    have h := congrArg (fun A => A.map GaussianInt.toComplex) (hRZ x)
    simp only [Matrix.map_mul, star_mapZ, realGenZ_map, gammaDZ_map, JZ_map] at h
    exact h
  have hmapsum : ∀ q : Fin 5 ⊕ Fin 10 → ℝ,
      (∑ x, (q x : ℂ) • realGen D x).map star = ∑ x, (q x : ℂ) • (realGen D x).map star := by
    intro q
    ext i j
    simp [Matrix.sum_apply, Matrix.map_apply, Complex.conj_ofReal]
  have hsum : ∀ q : Fin 5 ⊕ Fin 10 → ℝ,
      (∑ x, (q x : ℂ) • realGen D x) * M = M * (∑ x, (q x : ℂ) • realGen D x).map star := by
    intro q
    rw [hmapsum, Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hR x]
  have htrR : ∀ x, (realGen D x).trace = 0 := by
    intro x
    rw [realGen_eq, Matrix.trace_smul, gen_trace' x, smul_zero]
  have hMinv : M * M.map star = (countSign D.card : ℂ) • 1 := by
    have h := congrArg (fun A => A.map GaussianInt.toComplex) (gammaDZ_C_sq D)
    simp only [Matrix.map_mul, star_mapZ, gammaDZ_map, JZ_map] at h
    rw [h]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  have hcs : (countSign D.card : ℂ) ≠ 0 := by
    unfold countSign; split_ifs <;> simp
  constructor
  · rintro ⟨htr, hX⟩
    obtain ⟨p, q, hpq⟩ := realGen_real_comb D X htr
    set Y := ∑ x, (q x : ℂ) • realGen D x with hY
    set Z := ∑ x, (p x : ℂ) • realGen D x with hZ
    have hYc := hsum q
    have hZc := hsum p
    rw [← hY] at hYc
    rw [← hZ] at hZc
    have hstar : X.map star = Z.map star + (-Complex.I) • Y.map star := by
      rw [hpq]
      ext i j
      simp [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply]
    have hMY : M * Y.map star = 0 := by
      have e : X * M - M * X.map star = (2 * Complex.I) • (M * Y.map star) := by
        rw [hstar, hpq, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hZc, hYc]
        module
      rw [hX, sub_self] at e
      exact (smul_eq_zero.mp e.symm).resolve_left (by simp)
    have hY0 : Y = 0 := by
      have hinv : (((countSign D.card : ℂ))⁻¹ • M.map star) * M = 1 := by
        have h1 : M * (((countSign D.card : ℂ))⁻¹ • M.map star) = 1 := by
          rw [Matrix.mul_smul, hMinv, smul_smul, inv_mul_cancel₀ hcs, one_smul]
        exact mul_eq_one_comm.mp h1
      have hYs : Y.map star = 0 := by
        calc Y.map star = ((((countSign D.card : ℂ))⁻¹ • M.map star) * M) * Y.map star := by
              rw [hinv, Matrix.one_mul]
          _ = (((countSign D.card : ℂ))⁻¹ • M.map star) * (M * Y.map star) := by
              rw [Matrix.mul_assoc]
          _ = 0 := by rw [hMY, Matrix.mul_zero]
      ext i j
      have := congrFun (congrFun hYs i) j
      simpa using this
    have hq : ∀ x, (q x : ℂ) = 0 :=
      Fintype.linearIndependent_iff.mp (realGen_linearIndependent D) (fun x => (q x : ℂ))
        (by rw [← hY]; exact hY0)
    have hX' : X = Z := by
      rw [hpq, hY0, smul_zero, add_zero]
    rw [hX', hZ]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [Complex.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · intro hX
    rw [Submodule.mem_span_range_iff_exists_fun] at hX
    obtain ⟨p, rfl⟩ := hX
    have e : ∑ x, p x • realGen D x = ∑ x, (p x : ℂ) • realGen D x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.coe_smul]
    rw [e]
    refine ⟨?_, hsum p⟩
    rw [Matrix.trace_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.trace_smul, htrR x, smul_zero]

end Geometry

open Comparison.System.Geometry

/-- **Proposition 21 (four types of division).** Under the fifteen rotations a division (a subspace `D`
of P1's real six) is known by the dimension `k` of its smaller part: two divisions are carried one to
the other by a rotation of `SU(4)` exactly when they have the same type, there are four types,
`k = 0, 1, 2, 3`, each that of a coordinate division; in a basis, a division `D ⊆ {0, …, 5}` keeps
`C(k,2) + C(6−k,2) = 15, 10, 7, 6` and moves `k(6 − k) = 0, 5, 8, 9` of the fifteen generators,
each generator kept or moved and not both; its metric is `Σ_{a∉D} v_a² − Σ_{a∈D} v_a²`
(signature `(6−k, k)`); for the divisions of the lines with the singlet undivided (the Lemma), the
generators of the real form — the kept rotations and `i` times the moved ones — keep the form
`h_D = i^{r(r−1)/2}γ_D` (Hermitian, `h_D² = 1`, trace zero for `r = 2, 4`) when `r` is even and
commute with the antilinear `C_D = γ_DΘ`, `C_D² = −1` for `r = 1, 5` and `+1` for `r = 3`, when `r` is
odd; and on the balanced directions of the type `2|4` the metric has the signs `(+, −, −, −)` on
`v^⊥/ℝv`. Recognition: the four types are those of gravity, the weak force, electromagnetism and the
strong force; the real forms `su(4)`, `sl(2,ℍ)`, `su(2,2)`, `sl(4,ℝ)` of the twistor group; the balance
of `2|4` is spacetime `(1, 3)`. -/
theorem Geometry.four_kinds_statement :
    (∀ D D' : Division, Division.ByTurn D D' ↔ Division.kind D = Division.kind D') ∧
    (∀ D : Division, Division.kind D ≤ 3) ∧
    (∀ k ≤ 3, ∃ S : Finset (Fin 6), S.card = k ∧ Division.kind (Division.ofSet S) = k) ∧
    (∀ S : Finset (Fin 6), finrank ℝ (Division.ofSet S) = S.card) ∧
    (∀ D : Finset (Fin 6), (Finset.univ.filter (Kept D)).card =
      D.card.choose 2 + (6 - D.card).choose 2) ∧
    (∀ D : Finset (Fin 6), (Finset.univ.filter (Moved D)).card = D.card * (6 - D.card)) ∧
    (∀ (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10), Kept D x ↔ ¬ Moved D x) ∧
    (∀ (D : Finset (Fin 6)) (v : Fin 6 → ℝ),
      metricOf (Matrix.diagonal fun a => if a ∈ D then (1 : ℝ) else 0) v =
        ((∑ a, (if a ∈ D then 0 else v a ^ 2) - ∑ a, (if a ∈ D then v a ^ 2 else 0) : ℝ) : ℂ)) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 0 → ∀ x : Fin 5 ⊕ Fin 10,
      (realGen D x)ᴴ * hermForm D + hermForm D * realGen D x = 0) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 0 →
      (hermForm D)ᴴ = hermForm D ∧ hermForm D * hermForm D = 1 ∧
      (D.card ≠ 0 → (hermForm D).trace = 0)) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 1 → ∀ (x : Fin 5 ⊕ Fin 10) (v : Four → ℂ),
      realGen D x *ᵥ Cop D v = Cop D (realGen D x *ᵥ v)) ∧
    (∀ (D : Finset (Fin 5)) (v : Four → ℂ), Cop D (Cop D v) = (countSign D.card : ℂ) • v) ∧
    countSign 1 = -1 ∧ countSign 3 = 1 ∧ countSign 5 = -1 ∧
    (∀ v : Fin 6 → ℝ, GroupsContinuumLaw.OnCone v → GroupsContinuumLaw.r2 v = 1 →
      ∀ i j, GroupsContinuumLaw.g6 (GroupsContinuumLaw.frame v i) (GroupsContinuumLaw.frame v j) =
        if i = j then (if i = 0 then 1 else -1) else 0) ∧
    (∀ D : Finset (Fin 5), LinearIndependent ℂ (realGen D)) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 0 → ∀ X : Matrix Four Four ℂ,
      (X.trace = 0 ∧ Xᴴ * hermForm D + hermForm D * X = 0) ↔
        X ∈ Submodule.span ℝ (Set.range (realGen D))) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 1 → ∀ X : Matrix Four Four ℂ,
      (X.trace = 0 ∧ X * (gammaD D * J) = (gammaD D * J) * X.map star) ↔
        X ∈ Submodule.span ℝ (Set.range (realGen D))) ∧
    (∀ ε : Fin 6 → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) → ∀ X : Matrix (Fin 6) (Fin 6) ℝ, Xᵀ = -X →
      (GroupsContinuumLaw.realFormMap ε X)ᵀ * Matrix.diagonal ε +
        Matrix.diagonal ε * GroupsContinuumLaw.realFormMap ε X = 0) ∧
    (∀ ε : Fin 6 → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) → ∀ Y : Matrix (Fin 6) (Fin 6) ℝ,
      Yᵀ * Matrix.diagonal ε + Matrix.diagonal ε * Y = 0 →
        (GroupsContinuumLaw.realFormMap ε Y)ᵀ = -GroupsContinuumLaw.realFormMap ε Y ∧
          GroupsContinuumLaw.realFormMap ε (GroupsContinuumLaw.realFormMap ε Y) = Y) ∧
    (∀ (p q : ℕ) (v w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)), v ≠ 0 →
      ‖v.1‖ = ‖v.2‖ → w ≠ 0 → ‖w.1‖ = ‖w.2‖ →
        ((∃ c : ℝ, c ≠ 0 ∧ w = c • v) ↔
          (GroupsContinuumLaw.nrmPQ w = GroupsContinuumLaw.nrmPQ v ∨ GroupsContinuumLaw.nrmPQ w = -GroupsContinuumLaw.nrmPQ v))) ∧
    (∀ (p q : ℕ) (v : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)), v ≠ 0 →
      ‖v.1‖ = ‖v.2‖ → 0 < ‖v.1‖ ∧ ‖(GroupsContinuumLaw.nrmPQ v).1‖ = 1 ∧ ‖(GroupsContinuumLaw.nrmPQ v).2‖ = 1) := by
  refine ⟨byTurn_iff_kind, four_kinds_general.1, four_kinds_general.2, finrank_ofSet, card_kept,
    card_moved, kept_xor_moved, metric_ofSet, fun D hD x => lemma_division_even D hD x,
    hermForm_props, fun D hD x v => lemma_division_odd D hD x v, C_sq, by decide, by decide,
    by decide, fun v hv hr => (GroupsContinuumLaw.balanced_cone v hv hr).2.1, realGen_linearIndependent,
    fun D hD X => realGen_span_iff_even D hD X, fun D hD X => realGen_span_iff_odd D hD X,
    fun ε hε X hX => GroupsContinuumLaw.realFormMap_mem ε hε X hX,
    fun ε hε Y hY => GroupsContinuumLaw.realFormMap_onto ε hε Y hY,
    fun p q v w hv hvn hw hwn => GroupsContinuumLaw.null_line_iff v w hv hvn hw hwn,
    fun p q v hv hn => GroupsContinuumLaw.null_normalize v hv hn⟩

/-- **Proposition 22 (six divisions with the singlet fixed).** In a basis the divisions with the singlet
fixed are the 32 sets `S` of lines; the sixteen even ones are the sets of the two-spinor states `e_S`; on
P1's real six `γ_S ⊗ γ_S = θ_S` for every even `S`; dividing the singlet with the lines `D` is the same
division as dividing the lines outside `D`, so with the singlet fixed a division is known by the number
`r` of lines it divides; among the ten rotations that keep the singlet it keeps `C(r,2) + C(5−r,2)` and moves
`r(5 − r)` (`10/0, 6/4, 4/6, 4/6, 6/4, 10/0` for `r = 0, …, 5`); each keeps on `H` the product
`γ_D` of its divided lines, as a form when `r` is even and multiplied by the quaternionic structure when `r` is odd
(the Lemma); P3's own division is the point with the singlet: it keeps the ten and moves the five. -/
theorem prop_22 :
    Fintype.card (Finset (Fin 5)) = 32 ∧
    ((∀ k : Fin 16, Even (disagreeSet k).card) ∧ Function.Injective disagreeSet ∧
      ∀ S : Finset (Fin 5), Even S.card → ∃ k, disagreeSet k = S) ∧
    (∀ S : Finset (Fin 5), S.card % 2 = 0 → ∀ c : Fin 6,
      (gammaS S ⊗ₖ gammaS S) *ᵥ relOf (sixP1 c) =
        (if c ∈ linesDiv S then -1 else 1 : ℂ) • relOf (sixP1 c)) ∧
    (∀ D : Finset (Fin 5), (insert 0 (linesDiv D))ᶜ = linesDiv Dᶜ) ∧
    (∀ (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10), Kept Dᶜ x ↔ Kept D x) ∧
    (∀ D : Finset (Fin 5),
      (Finset.univ.filter fun f : Fin 10 => Kept (linesDiv D) (Sum.inr f)).card =
        D.card.choose 2 + (5 - D.card).choose 2 ∧
      (Finset.univ.filter fun f : Fin 10 => Moved (linesDiv D) (Sum.inr f)).card =
        D.card * (5 - D.card)) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 0 → ∀ x : Fin 5 ⊕ Fin 10,
      (realGen D x)ᴴ * hermForm D + hermForm D * realGen D x = 0) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 1 → ∀ (x : Fin 5 ⊕ Fin 10) (v : Four → ℂ),
      realGen D x *ᵥ Cop D v = Cop D (realGen D x *ᵥ v)) ∧
    (∀ D : Finset (Fin 5), Division.kind (Division.ofSet (linesDiv D)) = min D.card (6 - D.card)) ∧
    gammaS Finset.univ = 1 ∧
    (∀ t : Fin 5, gammaS (Finset.univ.erase t) = γ t ∨ gammaS (Finset.univ.erase t) = -γ t) ∧
    (∀ x : Fin 5 ⊕ Fin 10, Kept {1, 2, 3, 4, 5} x ↔ x.isRight) ∧
    [(∅ : Finset (Fin 6)), {0}, {1}, {0, 1}, {1, 2}, {0, 1, 2}].map
      (fun D => ((Finset.univ.filter (Kept D)).card, (Finset.univ.filter (Moved D)).card,
        (Finset.univ.filter fun f : Fin 10 => Kept D (Sum.inr f)).card,
        (Finset.univ.filter fun f : Fin 10 => Moved D (Sum.inr f)).card)) =
    [(15, 0, 10, 0), (10, 5, 10, 0), (10, 5, 6, 4), (7, 8, 6, 4), (7, 8, 4, 6), (6, 9, 4, 6)] := by
  refine ⟨by simp, disagreeSet_even, gamma_on_six, linesDiv_compl, kept_compl, kept_ten_lines,
    fun D hD x => lemma_division_even D hD x, fun D hD x v => lemma_division_odd D hD x v,
    fun D => by simp only [Division.kind, finrank_ofSet, card_linesDiv], gammaS_univ, gammaS_erase,
    P3_division_keeps_ten, six_divisions⟩

end Comparison.System
