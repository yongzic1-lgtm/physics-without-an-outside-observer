import Comparison.Elements.OneModelGeneral
import Comparison.Elements.OwnPast
import Comparison.Elements.Overlap
import Comparison.Elements.SixDirections
import Comparison.Elements.KeepL
import Comparison.Existence.Walk
import Comparison.Existence.Words
import Comparison.Existence.IharaBass
import Comparison.Existence.Gauge
import Comparison.Existence.Coin
import Comparison.Existence.PlaquetteData
import Comparison.Existence.Sign
import Comparison.Colour.ClosedAvailableTransitions
import Comparison.Colour.GramTerm
import Comparison.Mass.Harmonic
import Comparison.Mass.Angle
import Comparison.Law.Meetings
import Comparison.Law.Cover
import Comparison.Law.LongZero
import Comparison.WholePicture.Geometry
import Comparison.WholePicture.TheLaw
import Comparison.WholePicture.OneArc
import Comparison.WholePicture.Circulation
import Comparison.WholePicture.Green
import Comparison.Formulas.Kernel
import Comparison.GroupsContinuumLaw.Spin5
import Comparison.GroupsContinuumLaw.Rate
import Comparison.GroupsContinuumLaw.LogVertex
import Comparison.ArticleStatements.Geometry
import Comparison.WholePicture.Connection
import Comparison.WholePicture.SecondVariation
import Comparison.Existence.Plaquette
import Comparison.Existence.Motion
import Comparison.Existence.Excursion
import Comparison.Mass.Taylor
import Comparison.Elements.Divisions
import Comparison.Elements.Half
import Comparison.Law.Rule

/-!
# The proof system, part 0: one name for each object

Every object of the theory has one canonical
name. An object defined once in the project keeps its name (`J`, `Θ`, `γ`, `Ω`, `swap`, `Eop`, `L`,
`rel`, `transition`, `Adjacent`, `State`, `Continues`, `Partner`, ...). An object defined more than once
gets one name here, in the namespace `Comparison.System`, and every other definition of it is proved
equal to it (the *ties*); an existing theorem stated with another definition is carried over through
its tie.

* One system, the model: `ModelH := EuclideanSpace ℂ Four`, `modelΘ` (the quaternionic structure `Θ v = J v̄` on
  `ModelH`) and `modelPartner : Partner ModelH` (the model satisfies P3 (a)); `Jn 2 = J`.
* The five directions `γ`: `γZ_eq` (over `ℤ[i]`); `γ(n) = Σ n_s γ_s` is `gamma n` (`gE_eq_gamma`).
* `Sp2` (`GroupsContinuumLaw.Sp2`), with `mem_Sp2_iff_keeps_partner`.
* Two systems: `rel_zero_eq`, `Eop_eq_pairing'`, `L_eq_two_swap_Eop`.
* The Clebsch graph: `A R`, its adjacency over every commutative ring; ties with `adjacencyZ`,
  `Law.adjC`, `Law.adj16`, `Formulas.A16`, `WholePicture.adjZ`, `WholePicture.adjC`,
  `WholePicture.lapM`.
* The step `B R` over every commutative ring; ties with `stepOp transitionMat`, `contB`, `stepT`, `stepQ`,
  `stepR`, `WholePicture.Bc`, `GroupsContinuumLaw.lawQ`, `GroupsContinuumLaw.lawR`, `lawP`, `stepOp (Law.transitionK K)`.
* The signed step: `Aminus` (`sadjZ`, in the basis of the two-spinor states), `Bminus := stepOp lineOnRel`;
  tie with `Law.adjSigned`.
* The grade factor `kN` (`kR_eq_kN`).
* The sign of a division `theta R D` (ties `divSign`, `signD`, `thetaD`); the square root of the sign is `half D`.
* The chart `v t = e_t − 𝟏/5` is `vR t` (tie `vline_cast`).
* The step with a unitary connection `Bconn c := stepOp (WholePicture.connStep c)`
  (`Bconn_trivial`); the signed step over `ℝ` and `ℂ` (`sadj_eq`, `AC_eq`).
* The characters `charTable` and `Law.charX K = ¼ charTable` (`charX_eq`).
* The law `law u = det(I − uB)` (`lawPoly_eval_eq`), the excursion's first return `excursionGF` and the signed
  first return `Law.Phi`.
-/

namespace Comparison.System

open Matrix Complex
open scoped InnerProductSpace

/-! ## One system: the model -/

/-- The model's space of states, `ℂ⁴` with its inner product. -/
abbrev ModelH := EuclideanSpace ℂ Four

/-- The standard join on two quaternionic dimensions is `J`. -/
theorem Jn_two_eq : Jn 2 = J := Jn_two

/-- **The quaternionic structure of the model** on `ModelH`: `Θ v = J v̄`. -/
noncomputable def modelΘ (v : ModelH) : ModelH := WithLp.toLp 2 (Θ (WithLp.ofLp v))

theorem modelΘ_apply (v : ModelH) (p : Four) :
    modelΘ v p = (J *ᵥ star (WithLp.ofLp v)) p := rfl

/-- **The two models are one:** on `ModelH` the quaternionic structure is the matrix model's `Θ` through the
coordinates `WithLp.toLp`, `WithLp.ofLp`. -/
theorem modelΘ_toLp (v : Four → ℂ) : modelΘ (WithLp.toLp 2 v) = WithLp.toLp 2 (Θ v) := rfl

theorem ofLp_modelΘ (v : ModelH) : WithLp.ofLp (modelΘ v) = Θ (WithLp.ofLp v) := rfl

theorem inner_modelΘ (v w : ModelH) : ⟪modelΘ v, modelΘ w⟫_ℂ = ⟪w, v⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [modelΘ, Θ, J, ε, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    WithLp.ofLp_toLp]
  simp
  ring

/-- **The model satisfies P3 (a):** the quaternionic structure is additive, antilinear, antiunitary, and
`Θ² = −1`. -/
noncomputable def modelPartner : Partner ModelH where
  Θ := modelΘ
  map_add v w := by
    simp only [modelΘ, WithLp.ofLp_add, Θ_add, WithLp.toLp_add]
  map_smul c v := by
    simp only [modelΘ, WithLp.ofLp_smul, Θ_smul, WithLp.toLp_smul]
  inner_Θ := inner_modelΘ
  Θ_Θ v := by
    simp only [modelΘ, WithLp.ofLp_toLp, Θ_Θ, WithLp.toLp_neg, WithLp.toLp_ofLp]

theorem modelPartner_Θ (v : ModelH) : modelPartner.Θ v = modelΘ v := rfl

/-! ## The five directions -/

/-- `γ(n) = Σ_s n_s γ_s` for `n ∈ ℝ⁵` (`Elements/Overlap.lean`: `γv`). -/
noncomputable abbrev gamma (n : Fin 5 → ℝ) : Matrix Four Four ℂ := γv n

/-- The five directions over `ℤ[i]` are the five directions. -/
theorem γZ_eq (t : Fin 5) : (γZ t).map GaussianInt.toComplex = γ t := γZ_map t

/-- `GroupsContinuumLaw.gE` is `γ(n)` on `EuclideanSpace ℝ (Fin 5)`. -/
theorem gE_eq_gamma (x : GroupsContinuumLaw.E5) : GroupsContinuumLaw.gE x = gamma (WithLp.ofLp x) := rfl

/-! ## The rotations that keep the quaternionic structure -/

/-- **`Sp(2)`**, the unitary rotations of one system that keep the quaternionic structure (`GroupsContinuumLaw/Spin5.lean`). -/
abbrev Sp2 : Subgroup (Matrix.unitaryGroup Four ℂ) := GroupsContinuumLaw.Sp2

/-- **A unitary rotation is in `Sp(2)` exactly when it commutes with the quaternionic structure.** -/
theorem mem_Sp2_iff_keeps_partner (U : Matrix.unitaryGroup Four ℂ) :
    U ∈ Sp2 ↔ ∀ v, (U : Matrix Four Four ℂ) *ᵥ Θ v = Θ ((U : Matrix Four Four ℂ) *ᵥ v) := by
  have hU : (U : Matrix Four Four ℂ) * (U : Matrix Four Four ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  rw [keeps_partner_iff _ hU]
  rfl

/-! ## Two systems -/

/-- The two-spinor state `e_∅` is the singlet `Ω`. -/
theorem rel_zero_eq : rel 0 = Ω := rel_zero

/-- `E = |J⟩⟨J|`. -/
theorem Eop_eq_pairing' : Eop = vecMulVec (relOf J) (star (relOf J)) :=
  WholePicture.Eop_eq_pairing

/-- **The comparison is twice the swap and the singlet:** `L = 2(P + E)`. -/
theorem L_eq_two_swap_Eop : L = (2 : ℂ) • (swap + Eop) := L_eq_swap_singlet

/-! ## The Clebsch graph on the sixteen two-spinor states -/

/-- **The adjacency of the Clebsch graph** over any commutative ring:
`A_{xy} = Σ_t [x = transition t y]`. -/
def A (R : Type*) [CommRing R] : Matrix (Fin 16) (Fin 16) R :=
  ∑ t : Fin 5, Matrix.of fun x y => if x = transition t y then (1 : R) else 0

theorem A_apply (R : Type*) [CommRing R] (x y : Fin 16) :
    A R x y = ∑ t : Fin 5, if x = transition t y then (1 : R) else 0 := by
  simp [A, Matrix.sum_apply]

theorem card_transitions_between (x y : Fin 16) :
    (Finset.univ.filter fun t : Fin 5 => x = transition t y).card = if Adjacent y x then 1 else 0 := by
  revert x y
  decide

/-- The entries of the adjacency are one on the neighbours and zero elsewhere. -/
theorem A_apply_eq_ite (R : Type*) [CommRing R] (x y : Fin 16) :
    A R x y = if Adjacent y x then 1 else 0 := by
  rw [A_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, card_transitions_between]
  split_ifs <;> simp

theorem A_map (R : Type*) [CommRing R] : (A ℤ).map (Int.castRingHom R) = A R := by
  ext x y
  simp only [Matrix.map_apply, A_apply_eq_ite]
  split_ifs <;> simp

/-- `adjacencyZ` (`Existence/IharaBass.lean`) is the adjacency. -/
theorem adjacencyZ_eq : adjacencyZ = A ℤ := by
  ext x y
  simp [adjacencyZ, A, transitionMatZ, Matrix.sum_apply]

theorem sum_transitionMat_eq : (∑ t, transitionMat t) = A ℂ := by
  ext x y
  simp [transitionMat, transitionMatZ, A, Matrix.sum_apply]

/-- `Law.adjC` (`Law/Cover.lean`) is the adjacency over `ℂ`. -/
theorem law_adjC_eq : Law.adjC = A ℂ := sum_transitionMat_eq

/-- `Formulas.A16` (`Formulas/Kernel.lean`) is the adjacency over `ℂ`. -/
theorem formulas_A16_eq : Formulas.A16 = A ℂ := sum_transitionMat_eq

/-- `Law.adj16` (`Law/LongZero.lean`) is the adjacency over `ℝ`. -/
theorem law_adj16_eq : Law.adj16 = A ℝ := by
  ext x y
  simp [Law.adj16, Law.transitionK, A, Matrix.sum_apply]

/-- `WholePicture.adjZ`, the entrywise square of the signed step, is the adjacency. -/
theorem wholePicture_adjZ_eq (x y : Fin 16) : WholePicture.adjZ x y = A ℤ x y := by
  rw [A_apply_eq_ite]
  revert x y
  decide

/-- `WholePicture.adjC` is the adjacency over `ℂ`. -/
theorem wholePicture_adjC_eq : WholePicture.adjC = A ℂ := by
  ext x y
  rw [WholePicture.adjC, Matrix.of_apply, wholePicture_adjZ_eq, ← A_map ℂ]
  simp

/-- `WholePicture.lapM` is `5 − A` over `ℝ`. -/
theorem wholePicture_lapM_eq :
    WholePicture.lapM = (5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ := by
  ext x y
  rw [WholePicture.lapM, Matrix.of_apply, wholePicture_adjZ_eq, ← A_map ℝ]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
    smul_eq_mul, Int.coe_castRingHom]
  split_ifs <;> push_cast <;> ring

/-! ## The eighty states and the step `B` -/

/-- **The step of a world line** (Prop. 26): `B(x′, s; x, t) = [s ≠ t][x′ = x ⊕ g_s]`,
over any commutative ring. Entry `(s′, s)` is one when `s′` continues `s`. -/
def B (R : Type*) [CommRing R] : Matrix State State R :=
  Matrix.of fun s' s => if Continues s s' then 1 else 0

theorem B_apply (R : Type*) [CommRing R] (p q : State) :
    B R p q = if Continues q p then 1 else 0 := rfl

theorem B_map (R : Type*) [CommRing R] : (B ℤ).map (Int.castRingHom R) = B R := by
  ext p q
  simp only [Matrix.map_apply, B_apply]
  split_ifs <;> simp

/-- The matrix of `D_plus` (`Existence/IharaBass.lean`), `stepOp transitionMat`, is `B` over `ℂ`. -/
theorem stepOp_transitionMat_eq : stepOp transitionMat = B ℂ := by
  rw [← stepT_one_eq]
  rfl

/-- `contB` (`Existence/Coin.lean`) is `B` over `ℚ`. -/
theorem contB_eq : contB = B ℚ := rfl

/-- `stepT 1` (`Colour/ClosedAvailableTransitions.lean`) is `B`. -/
theorem stepT_one_eq_B (R : Type*) [CommRing R] : stepT (fun _ _ => (1 : R)) = B R := rfl

/-- `stepQ` (`Colour/ClosedAvailableTransitions.lean`) is `B` over `ℚ`. -/
theorem stepQ_eq : stepQ = B ℚ := rfl

/-- `stepR` (`Mass/Harmonic.lean`) is `B` over `ℝ`. -/
theorem stepR_eq : stepR = B ℝ := rfl

/-- `WholePicture.Bc` (`WholePicture/OneArc.lean`) is `B` over `ℂ`. -/
theorem wholePicture_Bc_eq : WholePicture.Bc = B ℂ := rfl

/-- `GroupsContinuumLaw.lawQ` (`GroupsContinuumLaw/Rate.lean`) is `B/4` over `ℚ`. -/
theorem groupsContinuumLaw_lawQ_eq : GroupsContinuumLaw.lawQ = (1 / 4 : ℚ) • B ℚ := by
  ext p q
  simp only [GroupsContinuumLaw.lawQ, Matrix.smul_apply, B_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- `GroupsContinuumLaw.lawR` (`GroupsContinuumLaw/LogVertex.lean`) is `B/4` over `ℝ`. -/
theorem groupsContinuumLaw_lawR_eq : GroupsContinuumLaw.lawR = (1 / 4 : ℝ) • B ℝ := by
  ext p q
  simp only [GroupsContinuumLaw.lawR, Matrix.smul_apply, B_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- `lawP` (`Mass/Angle.lean`) is `B/4` over `ℝ`. -/
theorem lawP_eq : lawP = (1 / 4 : ℝ) • B ℝ := rfl

/-- `stepOp (Law.transitionK K)` (`Law/Meetings.lean`) is `B` over every field of characteristic zero. -/
theorem stepOp_transitionK_eq (K : Type*) [Field K] [CharZero K] : stepOp (Law.transitionK K) = B K := by
  ext ⟨x', t'⟩ ⟨y, t⟩
  simp only [stepOp, Law.transitionK, Matrix.of_apply, B_apply, Continues]
  by_cases h1 : t' = t
  · simp [h1]
  · by_cases h2 : x' = transition t' y
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## The signed step -/

/-- **The signed step on the sixteen two-spinor states**, `A₋_{x y} = Σ_t [x = transition t y] ν(y, t)` in the
basis of the two-spinor states (`Existence/PlaquetteData.lean`: `sadjZ`). -/
abbrev Aminus : Matrix (Fin 16) (Fin 16) ℤ := sadjZ

/-- **The signed step on the eighty**, `B₋ = stepOp (γ_t ⊗ 1)`, the matrix of `D_minus`. -/
noncomputable abbrev Bminus : Matrix (Two × Fin 5) (Two × Fin 5) ℂ := stepOp lineOnRel

theorem transitionSign_values : ∀ t k, transitionSign t k = 1 ∨ transitionSign t k = -1 := by decide

/-- `Law.adjSigned` (`Law/Cover.lean`) is the signed step over `ℂ`. -/
theorem law_adjSigned_eq : Law.adjSigned = Aminus.map (Int.castRingHom ℂ) := by
  ext x y
  rw [Law.adjSigned, Matrix.sum_apply, Matrix.map_apply, Aminus, sadjZ_eq, Matrix.of_apply,
    map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [signTransitionC, Matrix.of_apply]
  by_cases h1 : x = transition t y
  · rcases transitionSign_values t y with h | h <;> simp [h1, h]
  · simp [h1]

/-! ## The grade factor -/

/-- `kR` over `ℝ` is `kN`. -/
theorem kR_eq_kN (N u : ℝ) : WholePicture.kR N u = WholePicture.kN N u := rfl

/-! ## The sign and the square root of the sign of a division -/

/-- **The sign of a division** `θ_D` on the six directions, over any ring: `−1` on the divided part
`D`, `+1` on the undivided part. -/
def theta (R : Type*) [Ring R] (D : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.diagonal fun c => if c ∈ D then -1 else 1

theorem divSign_eq (D : Finset (Fin 6)) : divSign D = theta ℤ D := rfl

theorem signD_eq (D : Finset (Fin 6)) : signD D = theta ℂ D := rfl

theorem thetaD_eq (D : Finset (Fin 6)) : thetaD D = theta ℝ D := rfl

/-- The half of a division is `half D` (`Elements/Half.lean`), `i` on `D` and `1` elsewhere. -/
theorem half_mul_self_eq_theta (D : Finset (Fin 6)) : half D * half D = theta ℂ D :=
  Comparison.half_mul_self D

/-! ## The chart -/

/-- `vline` over `ℚ` (`Existence/Motion.lean`) is the chart `vR` (`Mass/Taylor.lean`). -/
theorem vline_cast (t s : Fin 5) : ((vline t s : ℚ) : ℝ) = vR t s := by
  simp only [vline, vR]
  split_ifs <;> norm_num

/-! ## The step with a connection -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The step of a line carrying a unitary connection** on the links of the sixteen vertices. -/
noncomputable abbrev Bconn (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) :
    Matrix ((Fin 16 × n) × Fin 5) ((Fin 16 × n) × Fin 5) ℂ :=
  stepOp (WholePicture.connStep c)

/-- **With the trivial connection the step is `B ⊗ 1`.** -/
theorem Bconn_trivial (p q : (Fin 16 × n) × Fin 5) :
    Bconn (WholePicture.trivialConn (n := n)) p q =
      B ℂ (p.1.1, p.2) (q.1.1, q.2) * (1 : Matrix n n ℂ) p.1.2 q.1.2 := by
  simp only [Bconn, stepOp, Matrix.of_apply, WholePicture.connStep_trivial,
    Matrix.kroneckerMap_apply, B_apply, Continues, transitionMat, transitionMatZ, Matrix.map_apply]
  by_cases h1 : p.2 = q.2
  · simp [h1]
  · by_cases h2 : p.1.1 = transition p.2 q.1.1
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## The signed step over `ℝ` and `ℂ` -/

theorem sadj_eq : sadj = Aminus.map (Int.castRingHom ℝ) := rfl

theorem AC_eq : WholePicture.AC = Aminus.map (Int.castRingHom ℂ) := by
  ext x y
  simp [WholePicture.AC]

/-! ## The characters -/

theorem charX_eq (K : Type*) [Field K] [CharZero K] :
    Law.charX K = (1 / 4 : K) • charTable.map (Int.castRingHom K) := by
  ext U V
  simp only [Law.charX, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    eq_intCast]
  ring

/-! ## The law and its two first returns -/

/-- **The law** `D(u) = det(I − uB)`. -/
noncomputable def law (u : ℂ) : ℂ := (1 - u • B ℂ).det

theorem lawPoly_eval_eq (u : ℂ) : WholePicture.lawPoly.eval u = law u :=
  WholePicture.lawPoly_eval u

theorem law_eq_D_plus (u : ℂ) : law u = (1 - u • stepOp transitionMat).det := by
  rw [law, stepOp_transitionMat_eq]

/-- **The excursion's first return** `F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` (Prop. 29); its power
series
has the coefficients `excursionLaw n` (`Existence/Excursion.lean`: `excursion_gf`). -/
noncomputable def excursionGF (z : ℂ) : ℂ := z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)

theorem excursion_gf_eq (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (excursionLaw n : ℂ) * z ^ n) (excursionGF z) := excursion_gf z hz

/-- **The signed first return** is `Law.Phi z = −z⁴/(16 + 3z²)` (Prop. 30). -/
theorem signed_gf_eq (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (Law.Phi z) := signed_gf z hz

end Comparison.System
