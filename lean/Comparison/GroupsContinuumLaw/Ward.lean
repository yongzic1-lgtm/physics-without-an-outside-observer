import Comparison.ArticleStatements.Geometry
import Comparison.Elements.KeepL
import Comparison.Existence.Closing

/-!
# The local Ward identity at the singlet and its survival under elimination

The following finite statements are proved here.

* `ward_local`: with the clock leg `Γ_t = −P` and the gravity leg `Γ_g = E/4`,
  **`Γ_g − Γ_t = (6I − L)(3L + 2I)/32`**: the difference of the two vertices is the bare equation of
  motion `6I − L` times an operator; `ward_bass`: the same with `K₁₆(1/4) = (6I − L)/4`.
* `ward_legs`, `legs_on_singlet`: **both vertices are one on the singlet**:
  `Π Γ_t = Γ_t Π = Π Γ_g = Γ_g Π = Π`, `Π = E/4`; `ward_normalization_unique`: `−P` and `E/4` are the
  only multiples of `P` and `E` that are one on `Ω`.
* `two_source_singlet`: the single two-source operator `K₁₆(u) − j_t m Γ_t − j_g m Γ_g` has the singlet
  eigenvalue `1 − 5u + 4u² − m(j_t + j_g)`: one numerator `−m` for both sources.
* `connector_leg`: the connector `V v = Ω ⊗ v` gives `V†(Γ ⊗ M)V = 1 ⊗ M` (that is, `M`) for either
  leg and every internal matrix `M`.
* `regulated_inverse`, `same_pole_different_regular`, `regular_singlet_certificate`: with
  `K_b = (6I − L)/4`, `(K_b + μ)⁻¹ = μ⁻¹Π₀ + (μ+1)⁻¹Π_F + (μ+2)⁻¹Π_L`, the two legs have the same pole
  and different regular parts, `K_b(Π_F + Π_L/2) = 1 − Π₀`, `tr = 25/2`.
* `schur_equation_ideal` (**survival under source-bearing Schur elimination**): if two source
  derivatives differ by `UK + KV`, their reduced difference is `(LUI_A)S + S(I_AᵀVR)`, an element of the
  equation ideal of the reduced operator `S`; `schur_equation_ideal_on_shell`: so their on-shell
  numerators agree.
* `schur_homogeneous`, `schur_lapse_jet`, `on_shell_lapse_charge` (**lapse covariance**): the Schur
  complement of `c·K` is `c` times that of `K`; a lapse jet `K_N = K − zK_z` survives elimination,
  `L K_N R = S − z L K_z R`; at a rest zero the normalized lapse charge is `z`.
* `selfS_lapse`, `dressed_ward`: an explicit self-energy `S = ω − N m₀ − N²v²/(ω − N d)` is lapse
  covariant and its normalized lapse charge at the dressed pole `M` is `M` itself.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex Kronecker

/-! ## The two legs at the singlet -/

/-- The clock leg, the crossing normalized on the singlet: `Γ_t = −P`. -/
def clockLeg : Matrix Two Two ℂ := -swap

/-- The gravity leg, the join normalized on the singlet: `Γ_g = E/4`. -/
noncomputable def gravityLeg : Matrix Two Two ℂ := (1 / 4 : ℂ) • Eop

/-- The sixteen-vertex Bass operator in the comparison basis: `K₁₆(u) = (1 + u + 4u²)I − uL`. -/
noncomputable def bass16 (u : ℂ) : Matrix Two Two ℂ :=
  (1 + u + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • L

theorem L_two : L = (2 : ℂ) • swap + (2 : ℂ) • Eop := by
  rw [L_eq_swap_singlet, smul_add]

/-- **The local Ward identity at the singlet:** `Γ_g − Γ_t = (6I − L)(3L + 2I)/32`. -/
theorem ward_local :
    gravityLeg - clockLeg =
      ((6 : ℂ) • (1 : Matrix Two Two ℂ) - L) * ((1 / 32 : ℂ) • ((3 : ℂ) • L + (2 : ℂ) • 1)) := by
  rw [gravityLeg, clockLeg, L_two]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, ArticleStatements.swap_mul_swap, ArticleStatements.swap_mul_Eop,
    ArticleStatements.Eop_mul_swap, ArticleStatements.Eop_mul_Eop, smul_add, smul_sub, smul_smul, smul_neg]
  module

/-- The same identity with the critical Bass operator `K₁₆(1/4) = (6I − L)/4`. -/
theorem ward_bass :
    gravityLeg - clockLeg = bass16 (1 / 4) * ((1 / 8 : ℂ) • ((3 : ℂ) • L + (2 : ℂ) • 1)) := by
  rw [ward_local, bass16]
  have h : (1 + 1 / 4 + 4 * (1 / 4 : ℂ) ^ 2) = 3 / 2 := by norm_num
  rw [h]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

/-- **Both vertices are one on the singlet:** `Π Γ_t = Γ_t Π = Π Γ_g = Γ_g Π = Π`, `Π = E/4`. -/
theorem ward_legs :
    ArticleStatements.projSinglet * clockLeg = ArticleStatements.projSinglet ∧
      clockLeg * ArticleStatements.projSinglet = ArticleStatements.projSinglet ∧
      ArticleStatements.projSinglet * gravityLeg = ArticleStatements.projSinglet ∧
      gravityLeg * ArticleStatements.projSinglet = ArticleStatements.projSinglet := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ArticleStatements.projSinglet, clockLeg, Matrix.mul_neg, Matrix.smul_mul, ArticleStatements.Eop_mul_swap,
      smul_neg, neg_neg]
  · rw [ArticleStatements.projSinglet, clockLeg, Matrix.neg_mul, Matrix.mul_smul, ArticleStatements.swap_mul_Eop,
      smul_neg, neg_neg]
  · rw [ArticleStatements.projSinglet, gravityLeg, Matrix.smul_mul, Matrix.mul_smul, ArticleStatements.Eop_mul_Eop,
      smul_smul, smul_smul]
    norm_num
  · rw [ArticleStatements.projSinglet, gravityLeg, Matrix.smul_mul, Matrix.mul_smul, ArticleStatements.Eop_mul_Eop,
      smul_smul, smul_smul]
    norm_num

theorem Eop_mulVec_singlet : Eop *ᵥ Ω = (4 : ℂ) • Ω := by
  rw [Eop_mulVec, Ω_norm, mul_one]

theorem Ω_ne_zero : Ω ≠ 0 := by
  intro h
  have := Ω_norm
  rw [h] at this
  simp at this

/-- **The legs are one on the singlet:** `Γ_t Ω = Ω` and `Γ_g Ω = Ω`. -/
theorem legs_on_singlet : clockLeg *ᵥ Ω = Ω ∧ gravityLeg *ᵥ Ω = Ω := by
  refine ⟨?_, ?_⟩
  · rw [clockLeg, Matrix.neg_mulVec, ArticleStatements.swap_singlet, neg_neg]
  · rw [gravityLeg, Matrix.smul_mulVec, Eop_mulVec_singlet, smul_smul]
    norm_num

/-- **The normalization is unique:** a multiple of `P` or of `E` that is one on `Ω` is `−P` or
`E/4`. -/
theorem ward_normalization_unique (c d : ℂ) (hc : (c • swap) *ᵥ Ω = Ω)
    (hd : (d • Eop) *ᵥ Ω = Ω) : c = -1 ∧ d = 1 / 4 := by
  rw [Matrix.smul_mulVec, ArticleStatements.swap_singlet, smul_neg] at hc
  rw [Matrix.smul_mulVec, Eop_mulVec_singlet, smul_smul] at hd
  have hc' : (c + 1) • Ω = 0 := by
    calc (c + 1) • Ω = c • Ω + Ω := by rw [add_smul, one_smul]
      _ = c • Ω + -(c • Ω) := by rw [hc]
      _ = 0 := add_neg_cancel _
  have hd' : (d * 4 - 1) • Ω = 0 := by
    rw [sub_smul, one_smul, hd, sub_self]
  have h1 : c + 1 = 0 := by
    by_contra h
    exact Ω_ne_zero ((smul_eq_zero.mp hc').resolve_left h)
  have h2 : d * 4 - 1 = 0 := by
    by_contra h
    exact Ω_ne_zero ((smul_eq_zero.mp hd').resolve_left h)
  constructor
  · linear_combination h1
  · linear_combination h2 / 4

theorem L_mulVec_singlet : L *ᵥ Ω = (6 : ℂ) • Ω := by
  rw [L_two, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, ArticleStatements.swap_singlet,
    Eop_mulVec_singlet, smul_neg, smul_smul]
  module

/-- **One numerator for both sources:** the singlet block of `K₁₆(u) − j_t m Γ_t − j_g m Γ_g` is
`1 − 5u + 4u² − m(j_t + j_g)`. -/
theorem two_source_singlet (u jt jg m : ℂ) :
    (bass16 u - (jt * m) • clockLeg - (jg * m) • gravityLeg) *ᵥ Ω =
      (1 - 5 * u + 4 * u ^ 2 - m * (jt + jg)) • Ω := by
  obtain ⟨ht, hg⟩ := legs_on_singlet
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, bass16, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, L_mulVec_singlet, ht, Matrix.smul_mulVec, hg,
    smul_smul]
  module

/-! ## The connector `V v = Ω ⊗ v` -/

/-- The singlet as a column. -/
noncomputable def singletCol : Matrix Two Unit ℂ := Matrix.of fun a _ => Ω a

/-- The connector `V v = Ω ⊗ v`, from `Unit × n` (a copy of `n`) into `Two × n`. -/
noncomputable def connector (n : Type*) [DecidableEq n] : Matrix (Two × n) (Unit × n) ℂ :=
  singletCol ⊗ₖ (1 : Matrix n n ℂ)

theorem singletCol_sandwich (Γ : Matrix Two Two ℂ) :
    singletColᴴ * Γ * singletCol = Matrix.of fun _ _ => star Ω ⬝ᵥ (Γ *ᵥ Ω) := by
  ext i j
  simp only [singletCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The connector glues any internal matrix to a leg:** `V†(Γ ⊗ M)V = ⟨Ω, ΓΩ⟩ ⊗ M`. -/
theorem connector_sandwich {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix Two Two ℂ)
    (M : Matrix n n ℂ) :
    (connector n)ᴴ * (Γ ⊗ₖ M) * connector n =
      (Matrix.of fun _ _ => star Ω ⬝ᵥ (Γ *ᵥ Ω) : Matrix Unit Unit ℂ) ⊗ₖ M := by
  rw [connector, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, singletCol_sandwich, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem unit_one : (Matrix.of fun _ _ => (1 : ℂ) : Matrix Unit Unit ℂ) = 1 := by
  ext i j
  simp [Matrix.one_apply, Subsingleton.elim i j]

/-- **Both legs glue the same internal matrix:** `V†(Γ_t ⊗ M)V = V†(Γ_g ⊗ M)V = 1 ⊗ M`. -/
theorem connector_leg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (connector n)ᴴ * (clockLeg ⊗ₖ M) * connector n = (1 : Matrix Unit Unit ℂ) ⊗ₖ M ∧
      (connector n)ᴴ * (gravityLeg ⊗ₖ M) * connector n = (1 : Matrix Unit Unit ℂ) ⊗ₖ M := by
  obtain ⟨ht, hg⟩ := legs_on_singlet
  refine ⟨?_, ?_⟩
  · rw [connector_sandwich, ht, Ω_norm, unit_one]
  · rw [connector_sandwich, hg, Ω_norm, unit_one]

/-! ## The three projectors, and the same pole with different regular parts -/

local notation "Π₀" => ArticleStatements.projSinglet
local notation "Π_F" => ArticleStatements.projSymmetric
local notation "Π_L" => ArticleStatements.projVector

theorem proj_reverse : Π_F * Π₀ = 0 ∧ Π_L * Π₀ = 0 ∧ Π_L * Π_F = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ArticleStatements.projSymmetric, ArticleStatements.projSinglet]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
      ArticleStatements.swap_mul_Eop, smul_add, smul_neg, smul_smul]
    module
  · rw [ArticleStatements.projVector, ArticleStatements.projSinglet]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      ArticleStatements.swap_mul_Eop, ArticleStatements.Eop_mul_Eop, smul_sub, smul_neg, smul_smul]
    module
  · rw [ArticleStatements.projVector, ArticleStatements.projSymmetric]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, ArticleStatements.swap_mul_swap, ArticleStatements.Eop_mul_swap, smul_add,
      smul_sub, smul_neg, smul_smul]
    module

/-- Products of combinations of the three orthogonal projectors multiply their coefficients. -/
theorem proj_mul (a b c a' b' c' : ℂ) :
    (a • Π₀ + b • Π_F + c • Π_L) * (a' • Π₀ + b' • Π_F + c' • Π_L) =
      (a * a') • Π₀ + (b * b') • Π_F + (c * c') • Π_L := by
  obtain ⟨iN, iF, iL⟩ := ArticleStatements.proj_idem
  obtain ⟨oNF, oNL, oFL⟩ := ArticleStatements.proj_orth
  obtain ⟨oFN, oLN, oLF⟩ := proj_reverse
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, iN, iF, iL, oNF, oNL,
    oFL, oFN, oLN, oLF, smul_zero, add_zero, zero_add, smul_smul]
  all_goals module

theorem one_proj : (1 : Matrix Two Two ℂ) = (1 : ℂ) • Π₀ + (1 : ℂ) • Π_F + (1 : ℂ) • Π_L := by
  rw [one_smul, one_smul, one_smul, ArticleStatements.proj_sum]

/-- `K_b = (6I − L)/4`, the critical Bass operator on the sixteen. -/
noncomputable def kb : Matrix Two Two ℂ := (1 / 4 : ℂ) • ((6 : ℂ) • (1 : Matrix Two Two ℂ) - L)

theorem kb_eq : kb = (0 : ℂ) • Π₀ + (1 : ℂ) • Π_F + (2 : ℂ) • Π_L := by
  rw [kb, ArticleStatements.L_proj]
  conv_lhs => rw [← ArticleStatements.proj_sum]
  module

theorem swap_eq_proj : swap = (-1 : ℂ) • Π₀ + (1 : ℂ) • Π_F + (-1 : ℂ) • Π_L := by
  rw [ArticleStatements.projSinglet, ArticleStatements.projSymmetric, ArticleStatements.projVector]
  module

/-- **The regulated inverse:** `(K_b + μ)(μ⁻¹Π₀ + (μ+1)⁻¹Π_F + (μ+2)⁻¹Π_L) = 1`. -/
theorem regulated_inverse (μ : ℂ) (h0 : μ ≠ 0) (h1 : μ + 1 ≠ 0) (h2 : μ + 2 ≠ 0) :
    (kb + μ • (1 : Matrix Two Two ℂ)) * (μ⁻¹ • Π₀ + (μ + 1)⁻¹ • Π_F + (μ + 2)⁻¹ • Π_L) = 1 := by
  have hk : kb + μ • (1 : Matrix Two Two ℂ) = μ • Π₀ + (μ + 1) • Π_F + (μ + 2) • Π_L := by
    rw [kb_eq, one_proj]
    module
  rw [hk, proj_mul, mul_inv_cancel₀ h0, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, one_smul, one_smul,
    one_smul, ArticleStatements.proj_sum]

/-- **Same pole, different regular part:** with `G = μ⁻¹Π₀ + (μ+1)⁻¹Π_F + (μ+2)⁻¹Π_L`,
`Γ_t G Γ_t − Γ_g G Γ_g = (μ+1)⁻¹Π_F + (μ+2)⁻¹Π_L`: the singlet poles cancel, the regular parts stay. -/
theorem same_pole_different_regular (μ : ℂ) :
    clockLeg * (μ⁻¹ • Π₀ + (μ + 1)⁻¹ • Π_F + (μ + 2)⁻¹ • Π_L) * clockLeg -
      gravityLeg * (μ⁻¹ • Π₀ + (μ + 1)⁻¹ • Π_F + (μ + 2)⁻¹ • Π_L) * gravityLeg =
      (μ + 1)⁻¹ • Π_F + (μ + 2)⁻¹ • Π_L := by
  have ht : clockLeg = (1 : ℂ) • Π₀ + (-1 : ℂ) • Π_F + (1 : ℂ) • Π_L := by
    rw [clockLeg, swap_eq_proj]
    module
  have hg : gravityLeg = (1 : ℂ) • Π₀ + (0 : ℂ) • Π_F + (0 : ℂ) • Π_L := by
    rw [one_smul, zero_smul, zero_smul, add_zero, add_zero]
    rfl
  rw [ht, hg, proj_mul, proj_mul, proj_mul, proj_mul]
  module

/-- **The regular part at the singlet:** `K_b(Π_F + Π_L/2) = 1 − Π₀` and `tr(Π_F + Π_L/2) = 25/2`. -/
theorem regular_singlet_certificate :
    kb * (Π_F + (1 / 2 : ℂ) • Π_L) = 1 - Π₀ ∧ (Π_F + (1 / 2 : ℂ) • Π_L).trace = 25 / 2 := by
  obtain ⟨tN, tF, tL⟩ := ArticleStatements.trace_proj
  refine ⟨?_, ?_⟩
  · have h : Π_F + (1 / 2 : ℂ) • Π_L = (0 : ℂ) • Π₀ + (1 : ℂ) • Π_F + (1 / 2 : ℂ) • Π_L := by
      module
    rw [h, kb_eq, proj_mul, ← ArticleStatements.proj_sum]
    module
  · rw [Matrix.trace_add, Matrix.trace_smul, tF, tL, smul_eq_mul]
    norm_num

/-! ## Survival under source-bearing Schur elimination -/

section Transport

variable {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The retained coordinates, as a column block. -/
def retainIn (𝕜 : Type*) [Field 𝕜] (m n : Type*) [DecidableEq m] : Matrix (m ⊕ n) m 𝕜 :=
  Matrix.fromRows 1 0

/-- **A difference in the equation ideal survives elimination:** if two source derivatives differ by
`UK + KV`, then `L(UK + KV)R = (L U I_A) S + S (I_Aᵀ V R)`. No invertibility of `S` is assumed. -/
theorem schur_equation_ideal (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜)
    (D : Matrix n n 𝕜) [Invertible D] (U V : Matrix (m ⊕ n) (m ⊕ n) 𝕜) :
    schurL B D * (U * fromBlocks A B C D + fromBlocks A B C D * V) * schurR C D =
      (schurL B D * U * retainIn 𝕜 m n) * schurS A B C D +
        schurS A B C D * ((retainIn 𝕜 m n)ᵀ * V * schurR C D) := by
  have hKR : fromBlocks A B C D * schurR C D = retainIn 𝕜 m n * schurS A B C D := by
    rw [schur_KR, retainIn, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  have hLK : schurL B D * fromBlocks A B C D = schurS A B C D * (retainIn 𝕜 m n)ᵀ := by
    rw [schur_LK, retainIn, transpose_fromRows, Matrix.transpose_one, Matrix.transpose_zero,
      mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hKR]
    simp only [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, hLK]
    simp only [Matrix.mul_assoc]

/-- An equation-ideal difference has equal contractions on shell (any operator `K`). -/
theorem ward_mod_equation {p : Type*} [Fintype p] (K A C G T : Matrix p p 𝕜) (l r : p → 𝕜)
    (hL : l ᵥ* K = 0) (hR : K *ᵥ r = 0) (hV : G - T = A * K + K * C) :
    l ⬝ᵥ (G *ᵥ r) = l ⬝ᵥ (T *ᵥ r) := by
  have h : l ⬝ᵥ ((G - T) *ᵥ r) = 0 := by
    rw [hV, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero,
      dotProduct_zero, zero_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hL, zero_dotProduct]
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h
  exact h

/-- **On shell the two numerators agree after elimination:** contracting with null vectors of `S`
kills the reduced difference. -/
theorem schur_equation_ideal_on_shell (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜)
    (D : Matrix n n 𝕜) [Invertible D] (U V : Matrix (m ⊕ n) (m ⊕ n) 𝕜) (r l : m → 𝕜)
    (hr : schurS A B C D *ᵥ r = 0) (hl : l ᵥ* schurS A B C D = 0) :
    l ⬝ᵥ ((schurL B D * (U * fromBlocks A B C D + fromBlocks A B C D * V) * schurR C D) *ᵥ r) =
      0 := by
  have h := ward_mod_equation (schurS A B C D) (schurL B D * U * retainIn 𝕜 m n)
    ((retainIn 𝕜 m n)ᵀ * V * schurR C D)
    (schurL B D * (U * fromBlocks A B C D + fromBlocks A B C D * V) * schurR C D) 0 l r hl hr
    (by rw [sub_zero, schur_equation_ideal])
  rw [h, Matrix.zero_mulVec, dotProduct_zero]

/-- **Lapse covariance survives elimination:** the Schur complement of `c·K` is `c` times that of
`K` (the inverse of `D` written as the matrix inverse). -/
theorem schur_homogeneous (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜)
    (D : Matrix n n 𝕜) (c : 𝕜) (hc : c ≠ 0) (hD : IsUnit D.det) :
    c • A - (c • B) * (c • D)⁻¹ * (c • C) = c • (A - B * D⁻¹ * C) := by
  letI := invertibleOfNonzero hc
  have hinv : (c • D)⁻¹ = c⁻¹ • D⁻¹ := (Matrix.inv_smul D c hD).trans (by rw [invOf_eq_inv])
  rw [hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
  congr 2
  field_simp

/-- **The lapse jet survives elimination:** if `K_N = K − z K_z` then `L K_N R = S − z (L K_z R)`. -/
theorem schur_lapse_jet (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜)
    (D : Matrix n n 𝕜) [Invertible D] (Kz KN : Matrix (m ⊕ n) (m ⊕ n) 𝕜) (z : 𝕜)
    (hN : KN = fromBlocks A B C D - z • Kz) :
    schurL B D * KN * schurR C D = schurS A B C D - z • (schurL B D * Kz * schurR C D) := by
  rw [hN, Matrix.mul_sub, Matrix.sub_mul, schur_LKR, Matrix.mul_smul, Matrix.smul_mul]

/-- **At a rest zero the normalized lapse charge is the rest frequency:** if `K r = 0` and
`K_N = K − z K_z`, then `−(ℓ K_N r)/(ℓ K_z r) = z`. -/
theorem on_shell_lapse_charge {p : Type*} [Fintype p] (K Kz KN : Matrix p p 𝕜) (l r : p → 𝕜) (z : 𝕜)
    (hR : K *ᵥ r = 0) (hN : KN = K - z • Kz) (hd : l ⬝ᵥ (Kz *ᵥ r) ≠ 0) :
    -(l ⬝ᵥ (KN *ᵥ r)) / (l ⬝ᵥ (Kz *ᵥ r)) = z := by
  rw [hN, Matrix.sub_mulVec, hR, Matrix.smul_mulVec, zero_sub, dotProduct_neg, neg_neg,
    dotProduct_smul, smul_eq_mul, mul_div_assoc, div_self hd, mul_one]

end Transport

/-! ## A dressed rest operator -/

/-- The reduced pencil of `ωI − N[[m₀, v], [v, d]]`: `S = ω − N m₀ − N²v²/(ω − N d)`. -/
noncomputable def selfS (w N m0 d v : ℝ) : ℝ := w - N * m0 - N ^ 2 * v ^ 2 / (w - N * d)

/-- **The dressed pencil is lapse covariant:** `S(ω, N) = N S(ω/N, 1)`. -/
theorem selfS_lapse (w N m0 d v : ℝ) (hN : N ≠ 0) (hwd : w - N * d ≠ 0) :
    selfS w N m0 d v = N * selfS (w / N) 1 m0 d v := by
  have e : w / N - 1 * d = (w - N * d) / N := by field_simp
  rw [selfS, selfS, e]
  field_simp <;> ring

/-- **The normalized lapse charge at the dressed pole is the dressed pole:** with
`M − m₀ − v²/(M − d) = 0`, `(m₀ + 2v²/(M−d) + d v²/(M−d)²)/(1 + v²/(M−d)²) = M`. -/
theorem dressed_ward (M m0 d v : ℝ) (hMd : M ≠ d) (hpole : M - m0 - v ^ 2 / (M - d) = 0) :
    (m0 + 2 * v ^ 2 / (M - d) + d * v ^ 2 / (M - d) ^ 2) / (1 + v ^ 2 / (M - d) ^ 2) = M := by
  have hMd' : M - d ≠ 0 := sub_ne_zero.mpr hMd
  have hpos : 1 + v ^ 2 / (M - d) ^ 2 ≠ 0 := by
    have : 0 ≤ v ^ 2 / (M - d) ^ 2 := by positivity
    linarith
  rw [div_eq_iff hpos]
  have hm0 : m0 = M - v ^ 2 / (M - d) := by linarith
  rw [hm0]
  field_simp
  ring

end Comparison.GroupsContinuumLaw
