import Comparison.System.Geometry.Kept

/-!
# The geometry of comparison: the operators the ten rotations keep on three systems (Prop. 15, `N = 3`)

On three systems the operators kept by every
`U ⊗ U ⊗ U`, `U ∈ Sp(2)`, are exactly the sums of products of swaps and pairings, and they form a
space of dimension 14.

* **At most 14.** A kept `X` has its coefficients `c_σ(X) = Tr(P_σX)/64` along the strings of the
  sixteen observables. The five directions are rotations of `Sp(2)` with `γ_t†X_kγ_t = χ_t(k)X_k`, so `c_σ = 0`
  unless `χ_t(σ₀)χ_t(σ₁)χ_t(σ₂) = 1` for every `t` (256 strings, the third letter fixed by the first
  two). The ten quarter turns `(1 + γ_aγ_b)/√2` are rotations of `Sp(2)` with
  `U†X_kU = s_kX_{π k}`, so `c_σ = ±c_{π∘σ}`; a breadth-first forest (`gen3Tab`, `dep3Tab`, from
  `SEAT_G\work\kept_data.json`) joins each of the 256 strings to one of fourteen roots by such steps,
  each step lowering the depth: the fourteen root coefficients fix `X`.
* **At least 14.** Fourteen products of swaps and of `E₀₁` take, at fourteen chosen entries, an
  upper triangular matrix with nonzero diagonal (`M3`): they are independent.
-/

open scoped Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## The tables -/

/-- The third letter `c(a, b)` of a trivial-character string. -/
def third3 : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 15, 14, 13, 12, 11, 10], ![2, 6, 0, 10, 11, 12, 1, 15, 14, 13, 3, 4, 5, 9, 8, 7], ![3, 7, 10, 0, 13, 14, 15, 1, 12, 11, 2, 9, 8, 4, 5, 6], ![4, 8, 11, 13, 0, 15, 14, 12, 1, 10, 9, 2, 7, 3, 6, 5], ![5, 9, 12, 14, 15, 0, 13, 11, 10, 1, 8, 7, 2, 6, 3, 4], ![6, 2, 1, 15, 14, 13, 0, 10, 11, 12, 7, 8, 9, 5, 4, 3], ![7, 3, 15, 1, 12, 11, 10, 0, 13, 14, 6, 5, 4, 8, 9, 2], ![8, 4, 14, 12, 1, 10, 11, 13, 0, 15, 5, 6, 3, 7, 2, 9], ![9, 5, 13, 11, 10, 1, 12, 14, 15, 0, 4, 3, 6, 2, 7, 8], ![10, 15, 3, 2, 9, 8, 7, 6, 5, 4, 0, 13, 14, 11, 12, 1], ![11, 14, 4, 9, 2, 7, 8, 5, 6, 3, 13, 0, 15, 10, 1, 12], ![12, 13, 5, 8, 7, 2, 9, 4, 3, 6, 14, 15, 0, 1, 10, 11], ![13, 12, 9, 4, 3, 6, 5, 8, 7, 2, 11, 10, 1, 0, 15, 14], ![14, 11, 8, 5, 6, 3, 4, 9, 2, 7, 12, 1, 10, 15, 0, 13], ![15, 10, 7, 6, 5, 4, 3, 2, 9, 8, 1, 12, 11, 14, 13, 0]]

/-- The quarter turn that lowers the depth of `(a, b, c(a, b))`. -/
def gen3 : Fin 16 → Fin 16 → Fin 10 :=
  ![![0, 0, 0, 1, 2, 3, 0, 4, 5, 6, 1, 2, 3, 5, 6, 6], ![0, 0, 0, 4, 5, 6, 0, 4, 5, 6, 0, 7, 8, 5, 6, 8], ![0, 0, 0, 1, 2, 3, 0, 0, 7, 8, 1, 2, 3, 2, 3, 8], ![1, 4, 1, 1, 5, 6, 1, 4, 5, 6, 1, 2, 3, 5, 6, 6], ![2, 5, 2, 4, 2, 6, 7, 5, 5, 8, 2, 2, 8, 4, 6, 6], ![3, 6, 3, 4, 5, 3, 8, 6, 7, 6, 3, 7, 3, 5, 4, 5], ![0, 0, 0, 0, 7, 8, 0, 0, 7, 8, 0, 7, 8, 0, 9, 8], ![4, 4, 4, 4, 5, 6, 4, 4, 5, 6, 4, 4, 9, 5, 6, 6], ![5, 5, 7, 5, 5, 8, 7, 5, 5, 8, 5, 7, 8, 5, 6, 8], ![6, 6, 8, 6, 7, 6, 8, 6, 7, 6, 9, 8, 8, 6, 6, 7], ![1, 1, 1, 1, 2, 3, 1, 1, 1, 9, 1, 2, 3, 2, 3, 3], ![2, 7, 2, 2, 2, 8, 7, 2, 7, 8, 2, 2, 8, 2, 3, 8], ![3, 8, 3, 3, 7, 3, 8, 9, 8, 8, 3, 7, 3, 3, 3, 7], ![5, 5, 4, 5, 4, 5, 5, 5, 5, 6, 4, 4, 5, 5, 5, 6], ![6, 6, 4, 6, 6, 4, 9, 6, 6, 6, 4, 4, 4, 6, 6, 5], ![6, 8, 8, 6, 6, 5, 8, 6, 7, 8, 5, 8, 7, 6, 5, 6]]

/-- The depth of `(a, b, c(a, b))` in the forest. -/
def dep3 : Fin 16 → Fin 16 → ℕ :=
  ![![0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 2], ![1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3], ![1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3], ![1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2], ![1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2], ![0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2, 2, 0, 1, 1], ![1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2], ![1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3], ![1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3], ![1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2], ![1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2], ![1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 2], ![2, 2, 2, 2, 2, 3, 2, 2, 3, 3, 3, 2, 3, 2, 3, 3], ![2, 2, 2, 2, 3, 2, 3, 2, 2, 3, 3, 2, 2, 3, 2, 3], ![2, 3, 3, 2, 2, 2, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2]]

def rep3A : Fin 14 → Fin 16 := ![0, 0, 0, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6]

def rep3B : Fin 14 → Fin 16 := ![0, 1, 6, 0, 1, 2, 6, 10, 0, 1, 3, 6, 7, 13]

def pauliSignT : Fin 5 → Fin 16 → ℤ :=
  ![![1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1], ![1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1], ![1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1, 1], ![1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1], ![1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1]]

def cliffPermT : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 3, 4, 5, 6, 10, 11, 12, 7, 8, 9, 13, 14, 15], ![0, 3, 2, 1, 4, 5, 10, 7, 13, 14, 6, 11, 12, 8, 9, 15], ![0, 4, 2, 3, 1, 5, 11, 13, 8, 15, 10, 6, 12, 7, 14, 9], ![0, 5, 2, 3, 4, 1, 12, 14, 15, 9, 10, 11, 6, 13, 7, 8], ![0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 10, 13, 14, 11, 12, 15], ![0, 1, 4, 3, 2, 5, 8, 7, 6, 9, 13, 11, 15, 10, 14, 12], ![0, 1, 5, 3, 4, 2, 9, 7, 8, 6, 14, 15, 12, 13, 10, 11], ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 11, 10, 12, 13, 15, 14], ![0, 1, 2, 5, 4, 3, 6, 9, 8, 7, 12, 11, 10, 15, 14, 13], ![0, 1, 2, 3, 5, 4, 6, 7, 9, 8, 10, 12, 11, 14, 13, 15]]

def cliffSignT : Fin 10 → Fin 16 → ℤ :=
  ![![1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1], ![1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1], ![1, 1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1], ![1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, 1], ![1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1], ![1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1], ![1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1], ![1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, -1, 1, 1], ![1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1]]


def pos3W : Fin 14 → Fin 3 → Four :=
  ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (0, 1)], ![(0, 0), (0, 1), (0, 0)], ![(0, 0), (0, 1), (0, 1)], ![(0, 0), (0, 0), (0, 1)], ![(0, 0), (0, 1), (1, 0)], ![(0, 0), (0, 1), (0, 0)], ![(0, 0), (0, 1), (0, 0)], ![(0, 0), (0, 1), (0, 0)], ![(0, 0), (0, 0), (0, 1)], ![(0, 0), (0, 0), (0, 1)], ![(0, 0), (0, 0), (0, 1)], ![(0, 0), (1, 0), (1, 1)], ![(0, 0), (1, 0), (1, 1)]]

def pos3V : Fin 14 → Fin 3 → Four :=
  ![![(0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 1), (0, 0)], ![(0, 1), (0, 0), (0, 0)], ![(0, 1), (0, 1), (0, 0)], ![(0, 1), (0, 0), (0, 0)], ![(1, 0), (0, 1), (0, 0)], ![(1, 0), (1, 1), (0, 0)], ![(1, 0), (0, 0), (1, 1)], ![(0, 0), (1, 0), (1, 1)], ![(1, 0), (1, 1), (0, 0)], ![(1, 0), (0, 0), (1, 1)], ![(0, 0), (1, 0), (1, 1)], ![(0, 0), (0, 1), (0, 0)], ![(0, 0), (0, 0), (0, 1)]]


/-- The pairs of lines `(a, b)`, `a < b`, in the order of the ten symmetric states. -/
def pairA : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

def pairB : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

theorem pair_ne (f : Fin 10) : pairA f ≠ pairB f := by
  revert f; decide

/-! ## The sixteen observables over the Gaussian integers -/

/-- The sixteen observables with Gaussian integer entries. -/
def obsZ : Fin 16 → Matrix Four Four GaussianInt :=
  ![1, γZ 0, γZ 1, γZ 2, γZ 3, γZ 4,
    iZ • (γZ 0 * γZ 1), iZ • (γZ 0 * γZ 2), iZ • (γZ 0 * γZ 3), iZ • (γZ 0 * γZ 4),
    iZ • (γZ 1 * γZ 2), iZ • (γZ 1 * γZ 3), iZ • (γZ 1 * γZ 4),
    iZ • (γZ 2 * γZ 3), iZ • (γZ 2 * γZ 4), iZ • (γZ 3 * γZ 4)]

theorem obsZ_map (k : Fin 16) : (obsZ k).map GaussianInt.toComplex = obs k := by
  fin_cases k <;>
    simp [obsZ, obs, γZ_map, GroupsContinuumLaw.map_smulZ, Matrix.map_mul, GroupsContinuumLaw.toComplex_iZ,
      Matrix.map_one]

/-- **The five directions on the sixteen:** `γ_t X_k γ_t = χ_t(k) X_k`. -/
theorem gamma_conjZ : ∀ (t : Fin 5) (k : Fin 16),
    (γZ t)ᴴ * obsZ k * γZ t = ((pauliSignT t k : ℤ) : GaussianInt) • obsZ k := by
  decide +kernel

/-- **The quarter turns on the sixteen:** `(1 − F)X_k(1 + F) = 2s_kX_{π k}`, `F = γ_aγ_b`. -/
theorem cliff_conjZ : ∀ (f : Fin 10) (k : Fin 16),
    (1 - γZ (pairA f) * γZ (pairB f)) * obsZ k * (1 + γZ (pairA f) * γZ (pairB f)) =
      ((2 * cliffSignT f k : ℤ) : GaussianInt) • obsZ (cliffPermT f k) := by
  decide +kernel

theorem gamma_conj_obs (t : Fin 5) (k : Fin 16) :
    (γ t)ᴴ * obs k * γ t = ((pauliSignT t k : ℤ) : ℂ) • obs k := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (gamma_conjZ t k)
  simp only [Matrix.map_mul, GroupsContinuumLaw.map_conjTransposeZ, γZ_map, obsZ_map, GroupsContinuumLaw.map_smulZ,
    map_intCast] at h
  exact h

theorem qturn_conj_obs (f : Fin 10) (k : Fin 16) :
    (Article.qturn (pairA f) (pairB f))ᴴ * obs k * Article.qturn (pairA f) (pairB f) =
      ((cliffSignT f k : ℤ) : ℂ) • obs (cliffPermT f k) := by
  have hab := pair_ne f
  have h := congrArg (RingHom.mapMatrix GaussianInt.toComplex) (cliff_conjZ f k)
  simp only [map_mul, map_sub, map_add, map_one, RingHom.mapMatrix_apply, γZ_map, obsZ_map,
    GroupsContinuumLaw.map_smulZ, map_intCast] at h
  have hF : (γ (pairA f) * γ (pairB f))ᴴ = -(γ (pairA f) * γ (pairB f)) :=
    Article.γγ_conjTranspose hab
  have hs : star (((√2 : ℝ) : ℂ)⁻¹) = ((√2 : ℝ) : ℂ)⁻¹ := by simp
  rw [Article.qturn, Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, hF, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← sq, Article.sqrt2_inv_sq, ← sub_eq_add_neg, h, smul_smul]
  congr 1
  push_cast
  ring

/-! ## The rotations are in `Sp(2)` -/

theorem γ_unitary' (t : Fin 5) : γ t * (γ t)ᴴ = 1 := by
  rw [γ_conjTranspose, γ_mul_self]

theorem γ_keeps_J' (t : Fin 5) : γ t * J * (γ t)ᵀ = J := by
  rw [Matrix.mul_assoc, Article.J_γ_transpose, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]

/-- **A string of nontrivial character has no coefficient in a kept operator.** -/
theorem coef_zero_of_char {N : ℕ} (X : Op N) (hX : KeptN N X) (σ : Fin N → Fin 16) (t : Fin 5)
    (ht : ∏ i, ((pauliSignT t (σ i) : ℤ) : ℂ) = -1) : coef σ X = 0 := by
  have h := coef_of_commute (γ t) (γ_unitary' t) (fun k => ((pauliSignT t k : ℤ) : ℂ))
    (fun k => k) (fun k => gamma_conj_obs t k) X (hX (γ t) (γ_unitary' t) (γ_keeps_J' t)) σ
  have hc : ((fun k : Fin 16 => k) ∘ σ) = σ := rfl
  rw [hc, ht] at h
  have h2 : (2 : ℂ) * coef σ X = 0 := by linear_combination h
  simpa using h2

/-- **A quarter turn relates the coefficients of `σ` and `π ∘ σ`.** -/
theorem coef_eq_of_cliff {N : ℕ} (X : Op N) (hX : KeptN N X) (σ : Fin N → Fin 16) (f : Fin 10) :
    coef σ X = (∏ i, ((cliffSignT f (σ i) : ℤ) : ℂ)) * coef (cliffPermT f ∘ σ) X :=
  coef_of_commute (Article.qturn (pairA f) (pairB f)) (Article.qturn_unitary (pair_ne f)) _
    (cliffPermT f) (fun k => qturn_conj_obs f k) X
    (hX _ (Article.qturn_unitary (pair_ne f)) (Article.qturn_keeps_J (pair_ne f))) σ

/-! ## Three systems: at most fourteen -/

/-- The string `(a, b, c(a, b))`, `c` the letter that makes the character trivial. -/
def str3 (a b : Fin 16) : Fin 3 → Fin 16 := ![a, b, third3 a b]

/-- The string `(a, b, c)` has trivial character under the five directions. -/
def CharTriv (a b c : Fin 16) : Prop :=
  ∀ t : Fin 5, pauliSignT t a * pauliSignT t b * pauliSignT t c = 1

instance (a b c : Fin 16) : Decidable (CharTriv a b c) := by
  unfold CharTriv; infer_instance

theorem char_prod_cases : ∀ (t : Fin 5) (a b c : Fin 16),
    pauliSignT t a * pauliSignT t b * pauliSignT t c = 1 ∨
      pauliSignT t a * pauliSignT t b * pauliSignT t c = -1 := by
  decide +kernel

theorem cert3_unique : ∀ a b c : Fin 16, CharTriv a b c → c = third3 a b := by
  decide +kernel

theorem cert3_step : ∀ a b : Fin 16, dep3 a b = 0 ∨
    (dep3 (cliffPermT (gen3 a b) a) (cliffPermT (gen3 a b) b) < dep3 a b ∧
      cliffPermT (gen3 a b) (third3 a b) =
        third3 (cliffPermT (gen3 a b) a) (cliffPermT (gen3 a b) b)) := by
  decide +kernel

theorem cert3_rep : ∀ a b : Fin 16, dep3 a b = 0 → ∃ r : Fin 14, rep3A r = a ∧ rep3B r = b := by
  decide +kernel

/-- **The fourteen root coefficients fix a kept operator on three systems.** -/
theorem coef3_zero (X : Op 3) (hX : KeptN 3 X)
    (h : ∀ r : Fin 14, coef (str3 (rep3A r) (rep3B r)) X = 0) : ∀ σ, coef σ X = 0 := by
  have hstr : ∀ n, ∀ a b : Fin 16, dep3 a b = n → coef (str3 a b) X = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b hn
      rcases cert3_step a b with h0 | ⟨hlt, hthird⟩
      · obtain ⟨r, hra, hrb⟩ := cert3_rep a b h0
        rw [← hra, ← hrb]
        exact h r
      · have e := coef_eq_of_cliff X hX (str3 a b) (gen3 a b)
        have hcomp : cliffPermT (gen3 a b) ∘ str3 a b =
            str3 (cliffPermT (gen3 a b) a) (cliffPermT (gen3 a b) b) := by
          funext i
          fin_cases i
          · rfl
          · rfl
          · exact hthird
        have hz : coef (str3 (cliffPermT (gen3 a b) a) (cliffPermT (gen3 a b) b)) X = 0 :=
          ih _ (by omega) _ _ rfl
        rw [hcomp, hz, mul_zero] at e
        exact e
  intro σ
  by_cases hσ : CharTriv (σ 0) (σ 1) (σ 2)
  · have hs : σ = str3 (σ 0) (σ 1) := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact cert3_unique _ _ _ hσ
    rw [hs]
    exact hstr _ _ _ rfl
  · simp only [CharTriv, not_forall] at hσ
    obtain ⟨t, ht⟩ := hσ
    have hm := (char_prod_cases t (σ 0) (σ 1) (σ 2)).resolve_left ht
    apply coef_zero_of_char X hX σ t
    rw [Fin.prod_univ_three]
    exact_mod_cast hm

/-- The coefficient along a string, a linear map. -/
noncomputable def coefL {N : ℕ} (σ : Fin N → Fin 16) : Op N →ₗ[ℂ] ℂ where
  toFun X := coef σ X
  map_add' X Y := by simp only [coef, Matrix.mul_add, Matrix.trace_add, add_div]
  map_smul' c X := by
    simp only [coef, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply,
      mul_div_assoc]

/-- The kept operators on `N` systems, a complex vector space. -/
noncomputable def keptN (N : ℕ) : Submodule ℂ (Op N) := Subalgebra.toSubmodule (keptAlg N)

theorem finrank_kept3_le : finrank ℂ (keptN 3) ≤ 14 := by
  let φ : keptN 3 →ₗ[ℂ] (Fin 14 → ℂ) :=
    (LinearMap.pi fun r => coefL (str3 (rep3A r) (rep3B r))).comp (keptN 3).subtype
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hz : ∀ r, coef (str3 (rep3A r) (rep3B r)) X.1 = 0 := fun r => congrFun hX r
    exact Subtype.ext (eq_zero_of_coef X.1 (coef3_zero X.1 X.2 hz))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-! ## Three systems: at least fourteen -/

/-- The six permutations of three systems. -/
def perm3 : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 2]

def pepL : Fin 8 → Fin 6 := ![0, 0, 0, 1, 1, 1, 3, 3]

def pepR : Fin 8 → Fin 6 := ![0, 1, 4, 0, 1, 4, 0, 1]

/-- **Fourteen products of swaps and pairings on three systems:** the six `P_π` and eight
`P_π E₀₁ P_ρ`. -/
noncomputable def B3 (j : Fin 14) : Op 3 :=
  if h : j.val < 6 then permOp (perm3 ⟨j.val, h⟩)
  else permOp (perm3 (pepL ⟨j.val - 6, by omega⟩)) * Eab 0 1 *
    permOp (perm3 (pepR ⟨j.val - 6, by omega⟩))

/-- The quaternionic structure's matrix with integer entries. -/
def Jint (p q : Four) : ℤ :=
  if p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 1 then 1 else if p.1 = q.1 ∧ p.2 = 1 ∧ q.2 = 0 then -1 else 0

theorem JZ_eq_Jint (p q : Four) : JZ p q = ((Jint p q : ℤ) : GaussianInt) := by
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> decide

theorem J_apply_eq (p q : Four) : J p q = ((Jint p q : ℤ) : ℂ) := by
  rw [← JZ_map, Matrix.map_apply, JZ_eq_Jint, map_intCast]

def EabZ {N : ℕ} (a b : Fin N) (w v : Fin N → Four) : ℤ :=
  if (∀ c, c ≠ a → c ≠ b → w c = v c) then Jint (w a) (w b) * Jint (v a) (v b) else 0

theorem Eab_apply_eq {N : ℕ} (a b : Fin N) (w v : Fin N → Four) :
    Eab a b w v = ((EabZ a b w v : ℤ) : ℂ) := by
  unfold Eab EabZ
  simp only [Matrix.of_apply]
  split_ifs <;> simp [J_apply_eq]

def permZ {N : ℕ} (π : Fin N → Fin N) (w v : Fin N → Four) : ℤ := if v = w ∘ π then 1 else 0

theorem permOp_apply_eq {N : ℕ} (π : Equiv.Perm (Fin N)) (w v : Fin N → Four) :
    permOp π w v = ((permZ π w v : ℤ) : ℂ) := by
  unfold permOp permZ
  simp only [Matrix.of_apply]
  split_ifs <;> simp

def B3Z (j : Fin 14) (w v : Fin 3 → Four) : ℤ :=
  if h : j.val < 6 then permZ (perm3 ⟨j.val, h⟩) w v
  else EabZ 0 1 (w ∘ perm3 (pepL ⟨j.val - 6, by omega⟩))
    (v ∘ (perm3 (pepR ⟨j.val - 6, by omega⟩)).symm)

theorem B3_apply (j : Fin 14) (w v : Fin 3 → Four) : B3 j w v = ((B3Z j w v : ℤ) : ℂ) := by
  unfold B3 B3Z
  split_ifs with h
  · exact permOp_apply_eq _ w v
  · rw [mul_permOp_apply, permOp_mul_apply, Eab_apply_eq]

/-- The fourteen operators at the fourteen chosen entries, as a function. -/
def M3f (k j : Fin 14) : ℤ := B3Z j (pos3W k) (pos3V k)

/-- The fourteen operators at the fourteen chosen entries. -/
def M3 : Matrix (Fin 14) (Fin 14) ℤ := Matrix.of M3f

theorem M3f_upper : ∀ k j : Fin 14, k ≤ j ∨ M3f k j = 0 := by
  decide +kernel

theorem M3f_diag : ∀ k : Fin 14, M3f k k ≠ 0 := by
  decide +kernel

theorem M3_upper (k j : Fin 14) (h : j < k) : M3 k j = 0 :=
  (M3f_upper k j).resolve_left (not_le.mpr h)

theorem M3_diag (k : Fin 14) : M3 k k ≠ 0 := M3f_diag k

theorem M3_det : M3.det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (fun k j hjk => M3_upper k j hjk)]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => M3_diag k

theorem B3_linearIndependent : LinearIndependent ℂ B3 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hM : (M3.map (Int.cast : ℤ → ℂ)) *ᵥ g = 0 := by
    funext k
    have e := congrFun (congrFun hg (pos3W k)) (pos3V k)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, B3_apply] at e
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M3, M3f, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hdet : (M3.map (Int.cast : ℤ → ℂ)).det ≠ 0 := by
    have h := RingHom.map_det (Int.castRingHom ℂ) M3
    rw [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
    rw [← h]
    exact Int.cast_ne_zero.mpr M3_det
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hM)

/-! ## Every permutation of the systems is a product of swaps -/

theorem permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) : permOp π * permOp ρ = permOp (π * ρ) := by
  ext w v
  rw [permOp_mul_apply]
  simp only [permOp, Matrix.of_apply, Equiv.Perm.coe_mul]
  rfl

theorem permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext w v
  simp only [permOp, Matrix.of_apply, Equiv.Perm.coe_one, Function.comp_id, Matrix.one_apply]
  by_cases h : w = v
  · subst h; simp
  · simp [h, Ne.symm h]

theorem permOp_mem_brauer {N : ℕ} (π : Equiv.Perm (Fin N)) : permOp π ∈ brauerAlg N := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => rw [permOp_one]; exact (brauerAlg N).one_mem
  | swap_mul f x y hxy hf =>
    rw [← permOp_mul]
    exact (brauerAlg N).mul_mem (Algebra.subset_adjoin ⟨x, y, hxy, Or.inl rfl⟩) hf

theorem Eab_mem_brauer {N : ℕ} {a b : Fin N} (hab : a ≠ b) : Eab a b ∈ brauerAlg N :=
  Algebra.subset_adjoin ⟨a, b, hab, Or.inr rfl⟩

theorem B3_mem (j : Fin 14) : B3 j ∈ brauerAlg 3 := by
  unfold B3
  split_ifs
  · exact permOp_mem_brauer _
  · exact (brauerAlg 3).mul_mem ((brauerAlg 3).mul_mem (permOp_mem_brauer _)
      (Eab_mem_brauer (by decide))) (permOp_mem_brauer _)

/-! ## Three systems: exactly the products, dimension fourteen -/

theorem span_B3_le_brauer :
    Submodule.span ℂ (Set.range B3) ≤ Subalgebra.toSubmodule (brauerAlg 3) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact B3_mem j

theorem brauer_le_kept (N : ℕ) : Subalgebra.toSubmodule (brauerAlg N) ≤ keptN N :=
  fun _ hX => brauer_kept N hX

theorem keptN_three_eq : keptN 3 = Submodule.span ℂ (Set.range B3) := by
  have hle : Submodule.span ℂ (Set.range B3) ≤ keptN 3 :=
    span_B3_le_brauer.trans (brauer_le_kept 3)
  have hspan : finrank ℂ (Submodule.span ℂ (Set.range B3)) = 14 := by
    rw [finrank_span_eq_card B3_linearIndependent]
    simp
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hspan]
  exact finrank_kept3_le

theorem finrank_kept3 : finrank ℂ (keptN 3) = 14 := by
  rw [keptN_three_eq, finrank_span_eq_card B3_linearIndependent]
  simp

/-- **On three systems the kept operators are exactly the sums of products of swaps and pairings.** -/
theorem kept3_iff (X : Op 3) : KeptN 3 X ↔ X ∈ brauerAlg 3 := by
  constructor
  · intro hX
    have h : X ∈ keptN 3 := hX
    rw [keptN_three_eq] at h
    exact span_B3_le_brauer h
  · intro hX
    exact brauer_kept 3 hX

end Geometry

open Comparison.System.Geometry

/-- **Proposition 15 on three systems.** The operators on three quantities kept by every rotation of `Sp(2)`
are exactly the sums of products of swaps and pairings; they form a space of dimension 14, spanned by
the six permutations and eight products `P_πE₀₁P_ρ`, which are independent. Recognition: none. -/
theorem Geometry.kept_three_statement :
    (∀ X : Op 3, KeptN 3 X ↔ X ∈ brauerAlg 3) ∧ finrank ℂ (keptN 3) = 14 ∧
    keptN 3 = Submodule.span ℂ (Set.range B3) ∧ LinearIndependent ℂ B3 :=
  ⟨kept3_iff, finrank_kept3, keptN_three_eq, B3_linearIndependent⟩

end Comparison.System
