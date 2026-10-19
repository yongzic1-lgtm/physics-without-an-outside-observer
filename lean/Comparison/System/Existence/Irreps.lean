import Comparison.System.Existence.Matter
import Comparison.System.Existence.PairModel

/-!
# The proof system, the existence layer: what the ten keep on the two-spinor states (Proposition 48)

The ten rotations of one system act on the two-spinor states of two systems by
`T_f = γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b` (`f = {a, b}`), which on the two-spinor state `e_k = (B_k ⊗ 1)Ω` is the commutator,
`T_f e_k = ([γ_aγ_b, B_k] ⊗ 1)Ω = m(f, k) e_{k′}` (`tenAct_rel`, a Gaussian-integer identity). An operator that the ten
keep commutes with `1 + ½T_f²`, which is `±1` on each two-spinor state, and the signs of the ten separate the sixteen two-spinor states,
so it is diagonal in the two-spinor states; the ten connect the two-spinor states of the singlet, the symmetric or the vector states, so it is constant on the singlet, the symmetric or the vector states:
**the operators the ten keep are exactly the combinations of `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4`**
(`ten_commutant`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker
open scoped ComplexOrder

/-- The plane rotation `γ_aγ_b` of the plane `f`. -/
noncomputable def planeTurn (f : Fin 10) : Matrix Four Four ℂ := γ (Comparison.planeLines f).1 * γ (Comparison.planeLines f).2

/-- **The ten acting on two systems:** `T_f = γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b`. -/
noncomputable def tenAct (f : Fin 10) : Matrix Two Two ℂ := planeTurn f ⊗ₖ 1 + 1 ⊗ₖ planeTurn f

/-- The two-spinor state reached from `e_k` by the plane `f`. -/
def planeImg (f : Fin 10) (k : Fin 16) : Fin 16 := transition (Comparison.planeLines f).1 (transition (Comparison.planeLines f).2 k)

/-- The commutator of the plane rotation with `B_k`, over the Gaussian integers. -/
def commZ (f : Fin 10) (k : Fin 16) : Matrix Four Four GaussianInt :=
  γZ (Comparison.planeLines f).1 * γZ (Comparison.planeLines f).2 * relOpZ k - relOpZ k * (γZ (Comparison.planeLines f).1 * γZ (Comparison.planeLines f).2)

/-- Its coefficient on `B_{k′}`: `0` or `±2`. -/
def mZ (f : Fin 10) (k : Fin 16) : ℤ :=
  if commZ f k = (2 : GaussianInt) • relOpZ (planeImg f k) then 2
  else if commZ f k = (-2 : GaussianInt) • relOpZ (planeImg f k) then -2 else 0

theorem commZ_eq : ∀ (f : Fin 10) (k : Fin 16), commZ f k = (mZ f k : GaussianInt) • relOpZ (planeImg f k) := by
  decide +kernel

theorem ten_facts : (∀ f : Fin 10, ∀ k : Fin 16, planeImg f (planeImg f k) = k) ∧
    (∀ f : Fin 10, ∀ k : Fin 16, mZ f k ≠ 0 → mZ f (planeImg f k) = -mZ f k) ∧
    (∀ f : Fin 10, ∀ k : Fin 16, mZ f k ≠ 0 → (disagreeSet (planeImg f k)).card = (disagreeSet k).card) ∧
    (∀ f : Fin 10, ∀ k : Fin 16, mZ f k = 0 → planeImg f k = k ∨ True) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ _ _ => Or.inr trivial⟩

theorem one_kron_planeTurn_Ω (f : Fin 10) :
    ((1 : Matrix Four Four ℂ) ⊗ₖ planeTurn f) *ᵥ Ω = -((planeTurn f ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) := by
  have key : ∀ a b : Fin 5, a ≠ b → ((1 : Matrix Four Four ℂ) ⊗ₖ (γ a * γ b)) *ᵥ Ω =
      -(((γ a * γ b) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) := by
    intro a b hab
    have e1 : (1 : Matrix Four Four ℂ) ⊗ₖ (γ a * γ b) =
        ((1 : Matrix Four Four ℂ) ⊗ₖ γ a) * ((1 : Matrix Four Four ℂ) ⊗ₖ γ b) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have e2 : ((1 : Matrix Four Four ℂ) ⊗ₖ γ a) * (γ b ⊗ₖ (1 : Matrix Four Four ℂ)) =
        (γ b ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ γ a) := by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_one]
    rw [e1, ← Matrix.mulVec_mulVec, same_from_either_thing, Matrix.mulVec_mulVec, e2,
      ← Matrix.mulVec_mulVec, same_from_either_thing, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, γ_anticomm (Ne.symm hab), neg_kron, Matrix.neg_mulVec]
  exact key _ _ (Comparison.planeLines_ne f)

theorem tenAct_rel (f : Fin 10) (k : Fin 16) : tenAct f *ᵥ rel k = (mZ f k : ℂ) • rel (planeImg f k) := by
  have hc : planeTurn f * relOp k - relOp k * planeTurn f = (mZ f k : ℂ) • relOp (planeImg f k) := by
    have h := congrArg (fun M => M.map GaussianInt.toComplex) (commZ_eq f k)
    simp only [commZ, mapC_sub, mapC_mul, mapC_smul, γZ_map, relOpZ_map, map_intCast] at h
    rw [planeTurn]
    exact h
  have e : ((1 : Matrix Four Four ℂ) ⊗ₖ planeTurn f) * (relOp k ⊗ₖ (1 : Matrix Four Four ℂ)) =
      (relOp k ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ planeTurn f) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have h1 : (planeTurn f ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ rel k =
      ((planeTurn f * relOp k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
    rw [rel, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have h2 : ((1 : Matrix Four Four ℂ) ⊗ₖ planeTurn f) *ᵥ rel k =
      -(((relOp k * planeTurn f) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) := by
    rw [rel, Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, one_kron_planeTurn_Ω, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [tenAct, Matrix.add_mulVec, h1, h2, ← sub_eq_add_neg, ← Matrix.sub_mulVec, ← SysExt.sub_kron', hc,
    Matrix.smul_kronecker, Matrix.smul_mulVec]
  rfl

theorem tenAct_conjTranspose (f : Fin 10) : (tenAct f)ᴴ = -tenAct f := by
  have hF : (planeTurn f)ᴴ = -planeTurn f := by
    rw [planeTurn, Matrix.conjTranspose_mul, γ_conjTranspose, γ_conjTranspose, γ_anticomm (Ne.symm (Comparison.planeLines_ne f))]
  rw [tenAct, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, hF,
    Matrix.conjTranspose_one, neg_kron, SysExt.kron_neg', neg_add]

/-- The coefficient of an operator between two two-spinor states, `⟨e_k, X e_l⟩`. -/
noncomputable def relCoef (X : Matrix Two Two ℂ) (k l : Fin 16) : ℂ := star (rel k) ⬝ᵥ (X *ᵥ rel l)

theorem relCoef_comm {X : Matrix Two Two ℂ} (hX : ∀ f, X * tenAct f = tenAct f * X) (f : Fin 10)
    (k l : Fin 16) :
    (mZ f l : ℂ) * relCoef X k (planeImg f l) = -((mZ f k : ℂ) * relCoef X (planeImg f k) l) := by
  have h1 : star (rel k) ⬝ᵥ ((X * tenAct f) *ᵥ rel l) = (mZ f l : ℂ) * relCoef X k (planeImg f l) := by
    rw [← Matrix.mulVec_mulVec, tenAct_rel, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, relCoef]
  have h2 : star (rel k) ⬝ᵥ ((tenAct f * X) *ᵥ rel l) = -((mZ f k : ℂ) * relCoef X (planeImg f k) l) := by
    have hs : star (rel k) ᵥ* tenAct f = star ((tenAct f)ᴴ *ᵥ rel k) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hs, tenAct_conjTranspose, Matrix.neg_mulVec, tenAct_rel,
      star_neg, star_smul, neg_dotProduct, smul_dotProduct, relCoef, smul_eq_mul]
    congr 2
    simp
  rw [← h1, ← h2, hX f]

/-- The sign `ε(f, k)`: `1 + ½T_f²` on `e_k`. -/
def epsZ (f : Fin 10) (k : Fin 16) : ℤ := if mZ f k = 0 then 1 else -1

theorem mZ_values : ∀ (f : Fin 10) (k : Fin 16), mZ f k = 0 ∨ mZ f k = 2 ∨ mZ f k = -2 := by
  decide +kernel

theorem D_rel (f : Fin 10) (k : Fin 16) :
    (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f)) *ᵥ rel k = (epsZ f k : ℂ) • rel k := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, tenAct_rel,
    Matrix.mulVec_smul, tenAct_rel, smul_smul, ten_facts.1 f k, epsZ]
  by_cases hm : mZ f k = 0
  · rw [if_pos hm, hm]
    simp
  · rw [if_neg hm, ten_facts.2.1 f k hm]
    rcases mZ_values f k with h | h | h
    · exact absurd h hm
    · rw [h]
      push_cast
      module
    · rw [h]
      push_cast
      module

theorem D_conjTranspose (f : Fin 10) :
    (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f))ᴴ = 1 + (1 / 2 : ℂ) • (tenAct f * tenAct f) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    tenAct_conjTranspose, neg_mul_neg]
  congr 2
  simp

theorem eps_separates : ∀ k l : Fin 16, k ≠ l → ∃ f : Fin 10, epsZ f k ≠ epsZ f l := by
  decide +kernel

theorem irrep_paths : ∀ k l : Fin 16, (disagreeSet k).card = (disagreeSet l).card →
    k = l ∨ (∃ f : Fin 10, mZ f l ≠ 0 ∧ planeImg f l = k) ∨
      (∃ f g : Fin 10, mZ f l ≠ 0 ∧ mZ g (planeImg f l) ≠ 0 ∧ planeImg g (planeImg f l) = k) := by
  decide +kernel

theorem rel_expand (v : Two → ℂ) : v = ∑ k, (star (rel k) ⬝ᵥ v) • rel k := by
  set w := v - ∑ k, (star (rel k) ⬝ᵥ v) • rel k with hw
  have horth : ∀ j, star (rel j) ⬝ᵥ w = 0 := by
    intro j
    rw [hw, dotProduct_sub, dotProduct_sum]
    simp only [dotProduct_smul, rel_inner, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have hmem : w ∈ Submodule.span ℂ (Set.range rel) := by rw [rel_span]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hww : star w ⬝ᵥ w = 0 := by
    conv_lhs => arg 1; rw [← hc]
    rw [star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [star_smul, smul_dotProduct, horth, smul_zero]
  have : w = 0 := dotProduct_star_self_eq_zero.mp hww
  rw [hw, sub_eq_zero] at this
  exact this

theorem matrix_ext_rel {M N : Matrix Two Two ℂ} (h : ∀ k, M *ᵥ rel k = N *ᵥ rel k) : M = N := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext_on_range rel_span fun k => by simpa only [Matrix.toLin'_apply] using h k

/-- The combination `c₀Π₀ + c₁Π_F + c₂Π_L`. -/
noncomputable def irrepComb (c₀ c₁ c₂ : ℂ) : Matrix Two Two ℂ :=
  c₀ • ((1 / 4 : ℂ) • Eop) + c₁ • ((1 / 2 : ℂ) • (1 + swap)) + c₂ • ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop)

/-- The coefficient of the singlet, the symmetric or the vector states. -/
def irrepOf (c₀ c₁ c₂ : ℂ) (k : Fin 16) : ℂ :=
  if (disagreeSet k).card = 0 then c₀ else if (disagreeSet k).card = 2 then c₁ else c₂

theorem irrepComb_rel (c₀ c₁ c₂ : ℂ) (k : Fin 16) : irrepComb c₀ c₁ c₂ *ᵥ rel k = irrepOf c₀ c₁ c₂ k • rel k := by
  obtain ⟨p0, pF, pL⟩ := irrep_projectors k
  rw [irrepComb, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec c₀ ((1 / 4 : ℂ) • Eop),
    Matrix.smul_mulVec c₁ ((1 / 2 : ℂ) • (1 + swap)),
    Matrix.smul_mulVec c₂ ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop),
    p0, pF, pL, smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul, irrepOf]
  congr 1
  rcases irreps.1 k with h | h | h <;> simp [h]

/-- **The operators the ten keep are exactly the combinations of `Π₀`, `Π_F`, `Π_L`.** -/
theorem ten_commutant (X : Matrix Two Two ℂ) :
    (∀ f : Fin 10, X * tenAct f = tenAct f * X) ↔ ∃ c₀ c₁ c₂ : ℂ, X = irrepComb c₀ c₁ c₂ := by
  constructor
  · intro hX
    have hD : ∀ f, X * (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f)) =
        (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f)) * X := by
      intro f
      rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hX f, mul_assoc, hX f,
        ← mul_assoc]
    have hdiag : ∀ k l, k ≠ l → relCoef X k l = 0 := by
      intro k l hkl
      obtain ⟨f, hf⟩ := eps_separates k l hkl
      have e1 : star (rel k) ⬝ᵥ ((X * (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f))) *ᵥ rel l) =
          (epsZ f l : ℂ) * relCoef X k l := by
        rw [← Matrix.mulVec_mulVec, D_rel, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, relCoef]
      have e2 : star (rel k) ⬝ᵥ (((1 + (1 / 2 : ℂ) • (tenAct f * tenAct f)) * X) *ᵥ rel l) =
          (epsZ f k : ℂ) * relCoef X k l := by
        have hs : star (rel k) ᵥ* (1 + (1 / 2 : ℂ) • (tenAct f * tenAct f)) =
            star ((1 + (1 / 2 : ℂ) • (tenAct f * tenAct f))ᴴ *ᵥ rel k) := by
          rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hs, D_conjTranspose, D_rel, star_smul,
          smul_dotProduct, smul_eq_mul, relCoef]
        congr 1
        simp
      have e := e1.symm.trans ((congrArg (fun M => star (rel k) ⬝ᵥ (M *ᵥ rel l)) (hD f)).trans e2)
      have hne : (epsZ f l : ℂ) - epsZ f k ≠ 0 := by
        rw [sub_ne_zero]
        have hne' : epsZ f l ≠ epsZ f k := fun h => hf h.symm
        exact_mod_cast hne'
      have : ((epsZ f l : ℂ) - epsZ f k) * relCoef X k l = 0 := by rw [sub_mul, e, sub_self]
      exact (mul_eq_zero.mp this).resolve_left hne
    have hstep : ∀ f l, mZ f l ≠ 0 → relCoef X (planeImg f l) (planeImg f l) = relCoef X l l := by
      intro f l hm
      have h := relCoef_comm hX f (planeImg f l) l
      rw [ten_facts.1 f l, ten_facts.2.1 f l hm] at h
      have hm' : (mZ f l : ℂ) ≠ 0 := by exact_mod_cast hm
      push_cast at h
      have : (mZ f l : ℂ) * relCoef X (planeImg f l) (planeImg f l) = (mZ f l : ℂ) * relCoef X l l := by
        rw [h]
        ring
      exact mul_left_cancel₀ hm' this
    have hlayer : ∀ k l, (disagreeSet k).card = (disagreeSet l).card → relCoef X k k = relCoef X l l := by
      intro k l hkl
      rcases irrep_paths k l hkl with rfl | ⟨f, hm, rfl⟩ | ⟨f, g, hm, hm', rfl⟩
      · rfl
      · exact hstep f l hm
      · rw [hstep g _ hm', hstep f l hm]
    refine ⟨relCoef X 0 0, relCoef X 6 6, relCoef X 1 1, matrix_ext_rel fun l => ?_⟩
    rw [irrepComb_rel]
    have hexp := rel_expand (X *ᵥ rel l)
    rw [Finset.sum_eq_single l (fun k _ hk => by
      rw [show star (rel k) ⬝ᵥ (X *ᵥ rel l) = relCoef X k l from rfl, hdiag k l hk, zero_smul]) (by simp)] at hexp
    rw [hexp, show star (rel l) ⬝ᵥ (X *ᵥ rel l) = relCoef X l l from rfl, irrepOf]
    congr 1
    rcases irreps.1 l with h | h | h
    · have h0 : (disagreeSet (0 : Fin 16)).card = 0 := by decide
      rw [if_pos h]
      exact hlayer l 0 (by rw [h, h0])
    · have h6 : (disagreeSet (6 : Fin 16)).card = 2 := by decide
      rw [if_neg (by omega), if_pos h]
      exact hlayer l 6 (by rw [h, h6])
    · have h1 : (disagreeSet (1 : Fin 16)).card = 4 := by decide
      rw [if_neg (by omega), if_neg (by omega)]
      exact hlayer l 1 (by rw [h, h1])
  · rintro ⟨c₀, c₁, c₂, rfl⟩ f
    refine matrix_ext_rel fun l => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tenAct_rel, Matrix.mulVec_smul, irrepComb_rel,
      irrepComb_rel, Matrix.mulVec_smul, tenAct_rel, smul_smul, smul_smul]
    congr 1
    by_cases hm : mZ f l = 0
    · rw [hm]
      simp
    · rw [irrepOf, irrepOf, ten_facts.2.2.1 f l hm, mul_comm]

/-- **Proposition 48, the SI's wording:** the projectors onto the singlet, the symmetric and the vector states span the operators the ten keep: an operator on
two systems commutes with the ten rotations `γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b` exactly when it is `c₀Π₀ + c₁Π_F + c₂Π_L`. -/
theorem prop_48_kept (X : Matrix Two Two ℂ) :
    (∀ f : Fin 10, X * tenAct f = tenAct f * X) ↔
      ∃ c₀ c₁ c₂ : ℂ, X = c₀ • ((1 / 4 : ℂ) • Eop) + c₁ • ((1 / 2 : ℂ) • (1 + swap)) +
        c₂ • ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) :=
  ten_commutant X

end Comparison.System.Existence
