import Comparison.System.Postulates
import Comparison.Existence.Matter

/-!
# SI S3, statements 1 to 4: the five directions, the square root of the sign, one generation, the last-step direction's Gram

Each `S3_N` states the finite statement N of the Supplemental
Material, Section S3, as one Lean proposition, about the model; every candidate system is the model
up to one rotation (`System.uniqueness`).
-/

namespace Comparison.System

open Matrix Complex Polynomial
open scoped Kronecker

namespace S3

/-- The two-spinor state `(X ⊗ 1)Ω` made from the singlet by the operator `X` on the first system; under
`|J⟩ ↔ I` it is the operator `X`. -/
noncomputable def onSinglet (X : Matrix Four Four ℂ) : Two → ℂ :=
  (X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω

/-- A two-spinor state `(X ⊗ 1)Ω` with `X` unitary has length one. -/
theorem norm_onSinglet (X : Matrix Four Four ℂ) (hX : Xᴴ * X = 1) :
    star (onSinglet X) ⬝ᵥ onSinglet X = 1 := by
  rw [onSinglet, Ω, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one, dot_relOf,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX, Matrix.one_mul,
    Matrix.trace_mul_comm, MΩ_mul_conjTranspose, Matrix.trace_smul, Matrix.trace_one]
  norm_num

theorem plane_unitary (a b : Fin 5) : (γ a * γ b)ᴴ * (γ a * γ b) = 1 := by
  rw [Matrix.conjTranspose_mul, γ_conjTranspose, γ_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (γ a), γ_mul_self, Matrix.one_mul, γ_mul_self]

theorem line_unitary (a : Fin 5) : (γ a)ᴴ * γ a = 1 := by
  rw [γ_conjTranspose, γ_mul_self]

/-- Three times the charge is the sum of three times the line charges `0, 3, −1, −1, −1`. -/
theorem charge3_sum : ∀ h k : Fin 5, h ≠ k → ∀ r : Fin 16,
    ((∑ s ∈ disagreeSet r, (if s = k then (3 : ℤ) else if s = h then 0 else -1) : ℤ) : ℚ) =
      (charge3 h k r : ℚ) := by
  intro h k hk r
  congr 1
  revert h k r
  decide +kernel

theorem L_onSinglet (X : Matrix Four Four ℂ) (c : ℂ) (h : WholePicture.compOp X = c • X) :
    L *ᵥ onSinglet X = c • onSinglet X := by
  rw [onSinglet, WholePicture.L_on_operator, h, Matrix.smul_kronecker, Matrix.smul_mulVec]

/-- **The Gram of the last-step direction is the same at every last-step direction:** a unitary relabelling `V` of the five
directions carries the generators to `VXV†` and the last-step direction to `Ve`, and leaves every entry. -/
theorem gram_unitary_invariant (V : Matrix (Fin 5) (Fin 5) ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix (Fin 5) (Fin 5) ℂ) (e : Fin 5 → ℂ) :
    star ((V * X * Vᴴ) *ᵥ (V *ᵥ e)) ⬝ᵥ ((V * Y * Vᴴ) *ᵥ (V *ᵥ e)) = star (X *ᵥ e) ⬝ᵥ (Y *ᵥ e) := by
  have h1 : ∀ Z : Matrix (Fin 5) (Fin 5) ℂ, (V * Z * Vᴴ) *ᵥ (V *ᵥ e) = V *ᵥ (Z *ᵥ e) := by
    intro Z
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  rw [h1, h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hV,
    Matrix.one_mulVec]

end S3

open S3

/-- **SI S3, statement 1: five lines and one comparison.** Five Hermitian anticommuting directions
act on `ℂ⁴`, `γ_aγ_b + γ_bγ_a = 2δ_ab`, `γ_a† = γ_a`, `γ₁γ₂γ₃γ₄γ₅ = ±1`; the comparison
`L = I ⊗ I + Σ_t γ_t ⊗ γ_t = 2(P + E)` with `E = |J⟩⟨J|`, `Jᵀ = −J`, `E² = 4E`, `PE = EP = −E`;
`spec L = 6¹ ⊕ 2¹⁰ ⊕ (−2)⁵` with the eigenvectors (of length one) `(I ⊗ 1)Ω`, `(γ_aγ_b ⊗ 1)Ω`,
`(γ_a ⊗ 1)Ω` (the operators `I`, `γ_aγ_b`, `γ_a` under `|J⟩ ↔ I`). About the model; every
candidate system: `System.uniqueness`. -/
theorem S3_1 :
    (∀ a b : Fin 5,
      γ a * γ b + γ b * γ a = (if a = b then (2 : ℂ) else 0) • (1 : Matrix Four Four ℂ)) ∧
    (∀ a : Fin 5, (γ a)ᴴ = γ a) ∧
    (γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 ∨ γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = -1) ∧
    L = 1 ⊗ₖ 1 + ∑ t, γ t ⊗ₖ γ t ∧
    L = (2 : ℂ) • (swap + Eop) ∧
    Eop = vecMulVec (relOf J) (star (relOf J)) ∧
    Jᵀ = -J ∧
    Eop * Eop = (4 : ℂ) • Eop ∧
    swap * Eop = -Eop ∧ Eop * swap = -Eop ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) = 1 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 10 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) (-2)) = 5 ∧
    (∀ μ : ℂ, μ ≠ 6 → μ ≠ 2 → μ ≠ -2 → Module.End.eigenspace (Matrix.toLin' L) μ = ⊥) ∧
    (L *ᵥ onSinglet 1 = (6 : ℂ) • onSinglet 1 ∧ star (onSinglet 1) ⬝ᵥ onSinglet 1 = 1) ∧
    (∀ a b : Fin 5, a ≠ b →
      L *ᵥ onSinglet (γ a * γ b) = (2 : ℂ) • onSinglet (γ a * γ b) ∧
        star (onSinglet (γ a * γ b)) ⬝ᵥ onSinglet (γ a * γ b) = 1) ∧
    (∀ a : Fin 5,
      L *ᵥ onSinglet (γ a) = (-2 : ℂ) • onSinglet (γ a) ∧ star (onSinglet (γ a)) ⬝ᵥ onSinglet (γ a) = 1) := by
  refine ⟨clifford, γ_conjTranspose, Or.inl γ_prod, rfl, L_eq_swap_singlet,
    WholePicture.Eop_eq_pairing, J_transpose, ArticleStatements.Eop_mul_Eop, ArticleStatements.swap_mul_Eop,
    ArticleStatements.Eop_mul_swap, finrank_eigenspace_L_six, finrank_eigenspace_L_two,
    finrank_eigenspace_L_neg_two, eigenspace_L_other,
    ⟨L_onSinglet 1 6 WholePicture.compOp_one, norm_onSinglet 1 (by simp)⟩,
    fun a b hab => ⟨L_onSinglet _ 2 (WholePicture.compOp_plane hab), norm_onSinglet _ (plane_unitary a b)⟩,
    fun a => ⟨L_onSinglet _ (-2) (WholePicture.compOp_line a), norm_onSinglet _ (line_unitary a)⟩⟩

/-- **SI S3, statement 2: kept and moved rotations, the square root of the sign, and the algebra a description carries.**
(i) A division of the six directions (in the basis of Definition 16, a set `D`) keeps
`C(|D|, 2) + C(6 − |D|, 2)` and moves `|D|(6 − |D|)` of the fifteen rotations: `15, 10, 7, 6` and
`0, 5, 8, 9` at the four types `k|6 − k`. (ii) For every Hermitian projector `P`, the square root of the sign
`q = I − P + iP` has `q² = I − 2P = θ` and `q†q = I`. (iii) In every complex algebra whose words
multiply as `e_Se_T = c(S, T) e_{S△T}` (the 64 words of the six directions), the square root of the sign
`q_D(e_U) = i^{|U∩D|} e_U` satisfies `q_D(e_S) q_D(e_T) = (−1)^{|S∩T∩D|} q_D(e_Se_T)`. About the
model; every candidate system: `System.uniqueness`. -/
theorem S3_2 :
    (∀ D : Finset (Fin 6),
      (Finset.univ.filter (Kept D)).card = D.card.choose 2 + (6 - D.card).choose 2 ∧
      (Finset.univ.filter (Moved D)).card = D.card * (6 - D.card)) ∧
    ((Nat.choose 0 2 + Nat.choose 6 2, Nat.choose 1 2 + Nat.choose 5 2,
        Nat.choose 2 2 + Nat.choose 4 2, Nat.choose 3 2 + Nat.choose 3 2) = (15, 10, 7, 6) ∧
      (0 * 6, 1 * 5, 2 * 4, 3 * 3) = (0, 5, 8, 9)) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P : Matrix n n ℂ), P * P = P → Pᴴ = P →
      (1 - P + I • P) * (1 - P + I • P) = 1 - (2 : ℂ) • P ∧
        (1 - P + I • P)ᴴ * (1 - P + I • P) = 1) ∧
    (∀ (A : Type) [Ring A] [Algebra ℂ A] (e : Finset (Fin 6) → A)
      (c : Finset (Fin 6) → Finset (Fin 6) → ℂ), (∀ S T, e S * e T = c S T • e (symmDiff S T)) →
      ∀ D S T : Finset (Fin 6),
        (I ^ (S ∩ D).card • e S) * (I ^ (T ∩ D).card • e T) =
          ((-1 : ℂ) ^ (S ∩ T ∩ D).card) •
            ((c S T * I ^ ((symmDiff S T) ∩ D).card) • e (symmDiff S T))) :=
  ⟨fun D => ⟨card_kept D, card_moved D⟩, ⟨by decide, by decide⟩,
    fun _ _ _ P hP hH =>
      ⟨WholePicture.half_general P hP, WholePicture.half_general_unitary P hP hH⟩,
    fun _ _ _ e c he D S T => WholePicture.description_carries_product e c he D S T⟩

/-- **SI S3, statement 3: one generation.** For every plane `F = {h, k}` (`h ≠ k`) with the three
outside lines `C`: the hypercharge `Y(S) = |S∩F|/2 − |S∩C|/3`, the isospin
`T₃(S) = (|S∩{k}| − |S∩{h}|)/2` and the charge `Q(S)`, the sum over `S` of the line charges
`0, 1, −⅓, −⅓, −⅓` on `h, k, c₁, c₂, c₃`, satisfy `Q = T₃ + Y` on every even two-spinor state; the sixteen
hypercharges are `0, 1, −⅔, ⅙, ⅓, −½` with multiplicities `1, 1, 3, 6, 3, 2`; `ΣY = ΣY³ = 0`; the
sums of `Y` over the doublets (`|S∩F| = 1`) and over the triplets (`|S∩C| = 1, 2`) vanish;
`ΣY⁵ = 5/9`; the four lines beside the last-step direction pair in exactly three ways. Recognition: one generation
of matter. About the model; every candidate system: `System.uniqueness`. -/
theorem S3_3 :
    ∀ h k : Fin 5, h ≠ k →
      (∀ r : Fin 16, charge h k r =
        ∑ s ∈ disagreeSet r, (if s = k then (1 : ℚ) else if s = h then 0 else -1 / 3)) ∧
      (∀ r : Fin 16, charge h k r = isospin h k r + hyper h k r) ∧
      ((Finset.univ.filter fun r => hyper h k r = 0).card = 1 ∧
        (Finset.univ.filter fun r => hyper h k r = 1).card = 1 ∧
        (Finset.univ.filter fun r => hyper h k r = -2 / 3).card = 3 ∧
        (Finset.univ.filter fun r => hyper h k r = 1 / 6).card = 6 ∧
        (Finset.univ.filter fun r => hyper h k r = 1 / 3).card = 3 ∧
        (Finset.univ.filter fun r => hyper h k r = -1 / 2).card = 2) ∧
      ∑ r, hyper h k r = 0 ∧ ∑ r, hyper h k r ^ 3 = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper h k r = 0 ∧
      ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper h k r = 0 ∧
      ∑ r, hyper h k r ^ 5 = 5 / 9 ∧
      (WholePicture.pairingsBeside h).card = 3 := by
  intro h k hk
  obtain ⟨v0, v16, v23, v1, v13, v12⟩ := hyper_values h k hk
  obtain ⟨n1, n3, n5, n6, -, -⟩ := no_anomaly h k hk
  refine ⟨fun r => ?_, charge_eq h k hk, ⟨v0, v1, v23, v16, v13, v12⟩, n1, n3, n6, n5,
    WholePicture.hyper_fifth h k hk, WholePicture.three_pairings h⟩
  rw [charge_eq3, ← charge3_sum h k hk r]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> norm_num

/-- **SI S3, statement 4: the last-step direction's Gram.** On the twelve generators of `s(u(2) ⊕ u(3))`
(anti-Hermitian, of trace zero, block-diagonal on the plane and the three outside lines), orthonormal
in the trace form, the Gram matrix `G_XY = Re⟨Xφ, Yφ⟩` at the last-step direction `φ = e_h` has the characteristic
polynomial `X⁹(X − ½)²(X − 4/5)`: the nonzero eigenvalues `½, ½, 4/5` and nine zeros; the same
Gram at every last-step direction (a unitary relabelling `V` of the lines leaves every entry); and
`(½)/(4/5) = 5/8`, `1 − 5/8 = 3/8`. Recognition: `W±` at `½`, `Z` at `4/5`, the photon and the
eight colour rotations at zero; `M_W²/M_Z² = 5/8` and `sin²θ = 3/8` at the source. -/
theorem S3_4 :
    (∀ j : Fin 12, (WholePicture.gen12 j)ᴴ = -WholePicture.gen12 j ∧
      (WholePicture.gen12 j).trace = 0 ∧
      ∀ a b : Fin 5, WholePicture.inPlane a ≠ WholePicture.inPlane b →
        WholePicture.gen12 j a b = 0) ∧
    (∀ i j : Fin 12,
      ((WholePicture.gen12 i)ᴴ * WholePicture.gen12 j).trace.re = if i = j then 1 else 0) ∧
    (∀ i j : Fin 12, WholePicture.lastDirectionGram i j =
      (star (WholePicture.gen12 i *ᵥ WholePicture.lastDirectionE) ⬝ᵥ
        (WholePicture.gen12 j *ᵥ WholePicture.lastDirectionE)).re) ∧
    WholePicture.lastDirectionGram.charpoly = X ^ 9 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ)) ∧
    (∀ V : Matrix (Fin 5) (Fin 5) ℂ, Vᴴ * V = 1 → ∀ i j : Fin 12,
      (star ((V * WholePicture.gen12 i * Vᴴ) *ᵥ (V *ᵥ WholePicture.lastDirectionE)) ⬝ᵥ
        ((V * WholePicture.gen12 j * Vᴴ) *ᵥ (V *ᵥ WholePicture.lastDirectionE))).re =
          WholePicture.lastDirectionGram i j) ∧
    (1 / 2 : ℝ) / (4 / 5) = 5 / 8 ∧ 1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8 :=
  ⟨fun j => ⟨WholePicture.gen12_antiHermitian j, WholePicture.gen12_trace j,
    fun a b hab => WholePicture.gen12_block j a b hab⟩, WholePicture.gen12_orthonormal,
    fun _ _ => rfl, WholePicture.lastDirectionGram_charpoly,
    fun V hV i j => by rw [gram_unitary_invariant V hV]; rfl,
    WholePicture.source_ratios.1, WholePicture.source_ratios.2⟩

end Comparison.System
