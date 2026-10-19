import Comparison.System.Postulates
import Comparison.WholePicture.Connection
import Comparison.Formulas.OwnChart
import Comparison.Existence.Sign
import Comparison.Mass.Simple
import Comparison.WholePicture.TheLaw

/-!
# The proof system, the law: Proposition 54, the determinant, for every unitary connection

A unitary connection `U` of the sixteen vertices (`Connection (Fin 16) (unitaryGroup n ℂ)`, `U y x = (U x y)⁻¹`)
makes the step along the line `t` an operator on the vertices with their gauge,

  `Γ^σ_t[U]((y, i), (x, j)) = [y = x △ T_t] σ_t(x) U(y, x)_{ij}`,

with `σ = 1` (the count, `B₊[U]`) or `σ_t(x) = ν(x, t)` the Clifford sign of the transition (the sign, `B₋[U]`).
Here:

* `connStepSigned_herm`, `connStepSigned_sq`: **each `Γ^σ_t[U]` is a Hermitian involution**;
* `flipSign_conj`: the sign `s(x) = (−1)^{[a ∈ T_x]}`, `a ≠ t`, reverses it, `SΓS = −Γ`, so
  `det(1 − uΓ^σ_t[U]) = (1 − u²)^{8 dim U}` (`det_one_sub_connStepSigned`);
* `bass_connection`: **`det(I − uB^σ[U]) = (1 − u²)^{24 dim U} det((1 + 4u²) − uA^σ[U])` for every `u`**,
  `A^σ[U] = Σ_t Γ^σ_t[U]`, from Ihara and Bass (`ihara_bass`) by cancellation off `u² = 1`;
* `prop_54`: Proposition 54 as one statement.
-/

open Matrix Polynomial Comparison
open scoped Kronecker ComplexOrder

namespace Comparison.System

namespace Law

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The signs a step may carry -/

/-- A sign on the transitions: real, of square one, and the same on the two ends of a link. -/
def IsLinkSign (σ : Fin 5 → Fin 16 → ℂ) : Prop :=
  ∀ t x, star (σ t x) = σ t x ∧ σ t x * σ t x = 1 ∧ σ t (transition t x) = σ t x

/-- The count: every transition carries `1`. -/
def countSign : Fin 5 → Fin 16 → ℂ := fun _ _ => 1

/-- The Clifford sign of the transition, `ν(x, t)` with `(γ_t ⊗ 1) e_x = ν(x, t) e_{x △ T_t}`. -/
def cliffordSign : Fin 5 → Fin 16 → ℂ := fun t x => (transitionSign t x : ℂ)

theorem transitionSign_transition_eq : ∀ (t : Fin 5) (x : Fin 16), transitionSign t (transition t x) = transitionSign t x := by
  decide

theorem countSign_isLinkSign : IsLinkSign countSign := fun _ _ => by simp [countSign]

theorem cliffordSign_isLinkSign : IsLinkSign cliffordSign := by
  intro t x
  refine ⟨?_, ?_, ?_⟩
  · simp [cliffordSign]
  · rcases transitionSign_pm t x with h | h <;> simp [cliffordSign, h]
  · simp [cliffordSign, transitionSign_transition_eq]

/-! ## The step along one line, with a connection and a sign -/

/-- **The step along the line `t` with the connection `U` and the sign `σ`:**
`Γ^σ_t[U]((y, i), (x, j)) = [y = x △ T_t] σ_t(x) U(y, x)_{ij}`. -/
noncomputable def connStepSigned (σ : Fin 5 → Fin 16 → ℂ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    Matrix (Fin 16 × n) (Fin 16 × n) ℂ :=
  Matrix.of fun p q => if p.1 = transition t q.1 then σ t q.1 * WholePicture.turnMat c p.1 q.1 p.2 q.2 else 0

/-- With the count, the signed step is `WholePicture.connStep`. -/
theorem connStepSigned_count (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    connStepSigned countSign c t = WholePicture.connStep c t := by
  ext p q
  simp [connStepSigned, WholePicture.connStep, countSign]

/-- **`Γ^σ_t[U]` is Hermitian.** -/
theorem connStepSigned_herm {σ : Fin 5 → Fin 16 → ℂ} (hσ : IsLinkSign σ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    (connStepSigned σ c t)ᴴ = connStepSigned σ c t := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  simp only [connStepSigned, Matrix.of_apply]
  by_cases h : p.1 = transition t q.1
  · have h' : q.1 = transition t p.1 := (WholePicture.transition_eq_comm t q.1 p.1).mp h
    rw [ite_eq_left h', ite_eq_left h, WholePicture.turnMat_back c q.1 p.1, Matrix.conjTranspose_apply,
      star_mul', (hσ t p.1).1]
    congr 1
    rw [h, (hσ t q.1).2.2]
  · have h' : ¬ q.1 = transition t p.1 := fun h' => h ((WholePicture.transition_eq_comm t p.1 q.1).mp h')
    rw [ite_eq_right h', ite_eq_right h, star_zero]

/-- **`Γ^σ_t[U]` is an involution:** `Γ² = 1`. -/
theorem connStepSigned_sq {σ : Fin 5 → Fin 16 → ℂ} (hσ : IsLinkSign σ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    connStepSigned σ c t * connStepSigned σ c t = 1 := by
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (transition t q.1)]
  · have e2 := congrFun (congrFun (WholePicture.turnMat_mul_back c q.1 (transition t q.1)) p.2) q.2
    rw [Matrix.mul_apply] at e2
    simp only [connStepSigned, Matrix.of_apply, transition_transition, ↓reduceIte]
    by_cases h : p.1 = q.1
    · have hs : σ t (transition t q.1) * σ t q.1 = 1 := by rw [(hσ t q.1).2.2, (hσ t q.1).2.1]
      have e3 : ∀ x, σ t (transition t q.1) * WholePicture.turnMat c q.1 (transition t q.1) p.2 x *
          (σ t q.1 * WholePicture.turnMat c (transition t q.1) q.1 x q.2) =
          WholePicture.turnMat c q.1 (transition t q.1) p.2 x *
            WholePicture.turnMat c (transition t q.1) q.1 x q.2 := by
        intro x
        linear_combination (WholePicture.turnMat c q.1 (transition t q.1) p.2 x *
            WholePicture.turnMat c (transition t q.1) q.1 x q.2) * hs
      simp only [h, ↓reduceIte, e3, e2, Matrix.one_apply, Prod.ext_iff, true_and]
    · simp only [h, ↓reduceIte, zero_mul, Finset.sum_const_zero, Matrix.one_apply, Prod.ext_iff,
        false_and]
  · intro y _ hy
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [connStepSigned, Matrix.of_apply, ite_eq_right hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## A sign that reverses the step along one line -/

/-- A line other than `t`: the change `t` flips the agreement on it. -/
def otherLine (t : Fin 5) : Fin 5 := if t = 0 then 1 else 0

theorem otherLine_flips : ∀ (t : Fin 5) (x : Fin 16),
    (otherLine t ∈ disagreeSet (transition t x) ↔ ¬ otherLine t ∈ disagreeSet x) := by
  decide

/-- The sign `s(x) = (−1)^{[a ∈ T_x]}` with `a = otherLine t`, on the vertices with their gauge. -/
noncomputable def flipSign (t : Fin 5) : Matrix (Fin 16 × n) (Fin 16 × n) ℂ :=
  Matrix.diagonal fun p => if otherLine t ∈ disagreeSet p.1 then -1 else 1

theorem flipSign_sq (t : Fin 5) : flipSign (n := n) t * flipSign t = 1 := by
  rw [flipSign, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  split_ifs <;> norm_num

/-- **The sign reverses the step:** `S Γ^σ_t[U] S = −Γ^σ_t[U]`. -/
theorem flipSign_conj (σ : Fin 5 → Fin 16 → ℂ) (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ))
    (t : Fin 5) : flipSign t * connStepSigned σ c t * flipSign t = -connStepSigned σ c t := by
  ext p q
  simp only [flipSign, Matrix.diagonal_mul, Matrix.mul_diagonal, connStepSigned, Matrix.of_apply,
    Matrix.neg_apply]
  by_cases h : p.1 = transition t q.1
  · rw [ite_eq_left h]
    have hf := otherLine_flips t q.1
    rw [← h] at hf
    by_cases hq : otherLine t ∈ disagreeSet q.1
    · have hp : ¬ otherLine t ∈ disagreeSet p.1 := fun hp' => (hf.mp hp') hq
      simp only [hq, hp, ite_true, ite_false]
      ring
    · have hp : otherLine t ∈ disagreeSet p.1 := hf.mpr hq
      simp only [hq, hp, ite_true, ite_false]
      ring
  · simp [ite_eq_right h]

omit [DecidableEq n] in
theorem card_places_naming : Fintype.card (Fin 16 × n) = 2 * (8 * Fintype.card n) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  ring

/-- **The step along one line has `det(1 − uΓ^σ_t[U]) = (1 − u²)^{8 dim U}`.** -/
theorem det_one_sub_connStepSigned {σ : Fin 5 → Fin 16 → ℂ} (hσ : IsLinkSign σ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) (u : ℂ) :
    (1 - u • connStepSigned σ c t).det = (1 - u ^ 2) ^ (8 * Fintype.card n) :=
  Formulas.det_one_sub_signed_involution _ (flipSign t) (connStepSigned_sq hσ c t) (flipSign_sq t)
    (flipSign_conj σ c t) (8 * Fintype.card n) card_places_naming u

/-! ## Bass's identity with the connection -/

/-- **Proposition 54, the first line, for every unitary connection and either sign:**
`det(I − uB^σ[U]) = (1 − u²)^{24 dim U} det((1 + 4u²) − uA^σ[U])` for every `u`. -/
theorem bass_connection {σ : Fin 5 → Fin 16 → ℂ} (hσ : IsLinkSign σ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℂ) :
    (1 - u • stepOp (connStepSigned σ c)).det =
      (1 - u ^ 2) ^ (24 * Fintype.card n) *
        ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
          u • ∑ t, connStepSigned σ c t).det := by
  revert u
  refine extend_from_generic
    (p := (1 - (X : ℂ[X]) • (stepOp (connStepSigned σ c)).map C).det)
    (q := (1 - (X : ℂ[X]) ^ 2) ^ (24 * Fintype.card n) *
      ((1 + 4 * (X : ℂ[X]) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ[X]) -
        (X : ℂ[X]) • (∑ t, connStepSigned σ c t).map C).det)
    (det_one_sub_smul_poly _)
    (fun u => by rw [Polynomial.eval_mul, ← Formulas.det_vertex_poly]; simp) ?_
  intro u hu
  have h := ihara_bass (connStepSigned σ c) (connStepSigned_sq hσ c) u
  simp only [det_one_sub_connStepSigned hσ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_places_naming] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ (pow_ne_zero (56 * Fintype.card n) hc)
  linear_combination h

/-- **Below the critical step the law's operator is bounded below by `(1 − u)(1 − 4u)`**, for every unitary
connection and either sign. -/
theorem quad_lower_connection {σ : Fin 5 → Fin 16 → ℂ} (hσ : IsLinkSign σ)
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℝ) (hu : 0 ≤ u)
    (x : Fin 16 × n → ℂ) :
    (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
        (u : ℂ) • ∑ t, connStepSigned σ c t) *ᵥ x)).re :=
  RuleAndLaw.quad_lower (connStepSigned σ c) (connStepSigned_herm hσ c) (connStepSigned_sq hσ c) u hu x

/-! ## The closed forms and the critical step -/

/-- The polynomial `D₊(u)`. -/
noncomputable def DplusPoly : ℂ[X] :=
  (1 - X ^ 2) ^ 24 * (1 - X) * (1 - 4 * X) * (1 - X + 4 * X ^ 2) ^ 10 * (1 + 3 * X + 4 * X ^ 2) ^ 5

/-- `D₊(u) = (1 − 4u) g(u)` with `g(1/4) = 24 (15/16)²⁴`. -/
noncomputable def gPoly : ℂ[X] :=
  (1 - X ^ 2) ^ 24 * (1 - X) * (1 - X + 4 * X ^ 2) ^ 10 * (1 + 3 * X + 4 * X ^ 2) ^ 5

theorem gPoly_quarter : gPoly.eval (1 / 4) = 24 * (15 / 16) ^ 24 := by
  simp only [gPoly, eval_mul, eval_pow, eval_sub, eval_add, eval_one, eval_X, eval_mul, eval_ofNat]
  norm_num

/-- **At the critical step:** `D₊(u) = 24(15/16)²⁴(1 − 4u) + (1 − 4u)² h(u)` with `h` a polynomial. -/
theorem Dplus_at_quarter :
    ∃ h : ℂ[X], ∀ u : ℂ, (1 - u • stepOp transitionMat).det =
      24 * (15 / 16) ^ 24 * (1 - 4 * u) + (1 - 4 * u) ^ 2 * h.eval u := by
  obtain ⟨k, hk⟩ := Polynomial.dvd_iff_isRoot.mpr (show (gPoly - C (gPoly.eval (1 / 4))).IsRoot (1 / 4)
    by simp)
  refine ⟨-(C (1 / 4 : ℂ)) * k, fun u => ?_⟩
  rw [D_plus]
  have hu := congrArg (Polynomial.eval u) hk
  simp only [eval_sub, eval_C, eval_mul, eval_X] at hu
  rw [gPoly_quarter] at hu
  have hg : gPoly.eval u = (1 - u ^ 2) ^ 24 * (1 - u) * (1 - u + 4 * u ^ 2) ^ 10 *
      (1 + 3 * u + 4 * u ^ 2) ^ 5 := by
    simp only [gPoly, eval_mul, eval_pow, eval_sub, eval_add, eval_one, eval_X, eval_ofNat]
  rw [hg] at hu
  simp only [eval_mul, eval_neg, eval_C]
  linear_combination (1 - 4 * u) * hu

end Law

open Comparison.System.Law

/-- **Proposition 54, the determinant.** For every unitary connection `U` (of every rank `dim U`) and either
sign (the count `B₊[U]`, the Clifford sign `B₋[U]`), `det(I − uB±[U]) = (1 − u²)^{24 dim U} det((1 + 4u²) −
uA±[U])`; without a connection `D₊(u) = (1 − u²)²⁴(1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵` and
`D₋(u) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸` (`D₊` with the canonical step `B ℂ`, `stepOp_transitionMat_eq`); at `u = 1/4` only the factor `1 − 4u` vanishes,
`D₊(u) = 24(15/16)²⁴(1 − 4u) + O((1 − 4u)²)` and `D₋(1/4) = (15/16)²⁴(5/4)⁸`; for `0 ≤ u < 1/4` and every
unitary connection, `(1 + 4u²) − uA±[U] ≥ (1 − u)(1 − 4u) > 0`. -/
theorem prop_54 :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ))
        (u : ℂ),
      (1 - u • stepOp (Law.connStepSigned Law.countSign c)).det =
          (1 - u ^ 2) ^ (24 * Fintype.card n) *
            ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
              u • ∑ t, Law.connStepSigned Law.countSign c t).det ∧
        (1 - u • stepOp (Law.connStepSigned Law.cliffordSign c)).det =
          (1 - u ^ 2) ^ (24 * Fintype.card n) *
            ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
              u • ∑ t, Law.connStepSigned Law.cliffordSign c t).det) ∧
    (∀ u : ℂ, (1 - u • B ℂ).det =
      (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
        (1 + 3 * u + 4 * u ^ 2) ^ 5) ∧
    (∀ u : ℂ, (1 - u • stepOp (signTransitionC (-1 : ℂ))).det =
      (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8) ∧
    ((1 - (1 / 4 : ℂ) • B ℂ).det = 0 ∧
      (1 - (1 / 4 : ℂ) ^ 2) ^ 24 * (1 - 1 / 4) * (1 - 1 / 4 + 4 * (1 / 4) ^ 2) ^ 10 *
        (1 + 3 * (1 / 4) + 4 * (1 / 4 : ℂ) ^ 2) ^ 5 ≠ 0) ∧
    (∃ h : ℂ[X], ∀ u : ℂ, (1 - u • B ℂ).det =
      24 * (15 / 16) ^ 24 * (1 - 4 * u) + (1 - 4 * u) ^ 2 * h.eval u) ∧
    (1 - (1 / 4 : ℂ) • stepOp (signTransitionC (-1 : ℂ))).det = (15 / 16) ^ 24 * (5 / 4) ^ 8 ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ))
        (u : ℝ), 0 ≤ u → u < 1 / 4 → 0 < (1 - u) * (1 - 4 * u) ∧
      ∀ x : Fin 16 × n → ℂ,
        (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
            (u : ℂ) • ∑ t, Law.connStepSigned Law.countSign c t) *ᵥ x)).re ∧
        (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
            (u : ℂ) • ∑ t, Law.connStepSigned Law.cliffordSign c t) *ᵥ x)).re) := by
  simp only [← stepOp_transitionMat_eq]
  refine ⟨fun n _ _ c u => ⟨Law.bass_connection Law.countSign_isLinkSign c u,
      Law.bass_connection Law.cliffordSign_isLinkSign c u⟩, D_plus, D_minus_rel, D_plus_quarter,
    Law.Dplus_at_quarter, ?_, fun n _ _ c u hu0 hu => ⟨mul_pos (by linarith) (by linarith),
      fun x => ⟨Law.quad_lower_connection Law.countSign_isLinkSign c u hu0 x,
        Law.quad_lower_connection Law.cliffordSign_isLinkSign c u hu0 x⟩⟩⟩
  rw [D_minus_rel]
  norm_num

end Comparison.System
