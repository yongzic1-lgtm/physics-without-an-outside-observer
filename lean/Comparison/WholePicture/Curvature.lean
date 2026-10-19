module

public import Mathlib

/-!
# The whole picture, statement 15: the curvature identity at the last-step direction, `Λ = 3/ℓ²`

`LastDirectionSplit.lean` has `trace_five`
(`tr(γ_hγ_aγ_bγ_cγ_d) = 4ε_habcd`), `trace_lastDirection_curv`, the expansion `mm_expand` and
`lambda_from_ratio`. Here the identity is closed on the four directions that move the last-step direction, with the
form indices kept: `R_{abef}` is a curvature (antisymmetric in its form pair),
`E_{abef} = δ_aeδ_bf − δ_afδ_be` the frame two-form `e^a ∧ e^b`, and on pairs `p = (a, b)` of
directions `X ∧ Y = ¼ Σ ε_{pr} X_{pq} Y_{rs} ε_{qs}`, the full contraction
`¼ ε_{abcd} ε_{efgh} X_{abef} Y_{cdgh}`.

* `eps_frameP`, `eps_epsP`, `frame_epsP`, `eps_eps_leftP`: `Σ_s E_{rs} ε_{qs} = 2ε_{qr}`,
  `Σ_r ε_{pr} ε_{qr} = 2E_{pq}` and their mirrors (kernel checks on the four directions).
* `wedge_R_E`, `wedge_E_R`: `R ∧ E = E ∧ R = 2R`, `R = Σ_{ab} R_{abab}`; `wedge_E_E`: `E ∧ E = 24`.
* `curvature_identity`: **`(R − E/ℓ²) ∧ (R − E/ℓ²) − R ∧ R = −(4/ℓ²)(R − 6/ℓ²)`**; `lambda_three`:
  the volume term `24/ℓ⁴` is `(4/ℓ²)·2Λ` exactly at **`Λ = 3/ℓ²`**.
-/

@[expose] public section

namespace Comparison.WholePicture

/-- The Levi-Civita symbol of four directions, the sign of the Vandermonde product. -/
def eps4 (a b c d : Fin 4) : ℤ :=
  Int.sign (((b : ℤ) - a) * ((c : ℤ) - a) * ((d : ℤ) - a) * ((c : ℤ) - b) * ((d : ℤ) - b) *
    ((d : ℤ) - c))

/-- The frame two-form `E_{abef} = δ_aeδ_bf − δ_afδ_be`. -/
def frameZ (a b e f : Fin 4) : ℤ :=
  (if a = e ∧ b = f then 1 else 0) - (if a = f ∧ b = e then 1 else 0)

theorem eps_frame_Z : ∀ c d e f : Fin 4,
    ∑ g, ∑ h, frameZ c d g h * eps4 e f g h = 2 * eps4 e f c d := by decide

theorem eps_eps_Z : ∀ a b e f : Fin 4,
    ∑ c, ∑ d, eps4 a b c d * eps4 e f c d = 2 * frameZ a b e f := by decide

theorem frame_eps_Z : ∀ a b g h : Fin 4,
    ∑ e, ∑ f, frameZ a b e f * eps4 e f g h = 2 * eps4 a b g h := by decide

theorem eps_eps_left_Z : ∀ c d g h : Fin 4,
    ∑ a, ∑ b, eps4 a b c d * eps4 a b g h = 2 * frameZ c d g h := by decide

theorem frame_diag_Z : ∑ a, ∑ b, (frameZ a b a b - frameZ a b b a) = 24 := by decide

/-- The frame two-form is antisymmetric in its form pair. -/
theorem frameZ_antisymm : ∀ a b e f : Fin 4, frameZ a b f e = -frameZ a b e f := by decide

/-- A pair of directions: an internal pair `(a, b)` or a form pair `(e, f)`. -/
abbrev Pair := Fin 4 × Fin 4

/-- `ε` on pairs: `ε_{(a,b),(c,d)} = ε_{abcd}`. -/
def epsP (p q : Pair) : ℝ := (eps4 p.1 p.2 q.1 q.2 : ℝ)

/-- The frame two-form on pairs. -/
def frameP (p q : Pair) : ℝ := (frameZ p.1 p.2 q.1 q.2 : ℝ)

/-- A four-index tensor read on pairs. -/
def onPairs (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (p q : Pair) : ℝ := R p.1 p.2 q.1 q.2

/-- **The pairing of two curvature two-forms:** `X ∧ Y = ¼ Σ ε_{pr} X_{pq} Y_{rs} ε_{qs}`. -/
noncomputable def wedge (X Y : Pair → Pair → ℝ) : ℝ :=
  (1 / 4) * ∑ p, ∑ r, ∑ q, ∑ s, epsP p r * X p q * Y r s * epsP q s

/-- The scalar curvature `R = Σ_{ab} R_{abab}`. -/
def scalarR (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ := ∑ a, ∑ b, R a b a b

theorem sum_pair (f : Pair → ℝ) : ∑ p, f p = ∑ a, ∑ b, f (a, b) := Fintype.sum_prod_type _

theorem eps_frameP (r q : Pair) : ∑ s, frameP r s * epsP q s = 2 * epsP q r := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (eps_frame_Z r.1 r.2 q.1 q.2)
  push_cast at h
  rw [sum_pair]
  simpa only [frameP, epsP] using h

theorem eps_epsP (p q : Pair) : ∑ r, epsP p r * epsP q r = 2 * frameP p q := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (eps_eps_Z p.1 p.2 q.1 q.2)
  push_cast at h
  rw [sum_pair]
  simpa only [frameP, epsP] using h

theorem frame_epsP (p s : Pair) : ∑ q, frameP p q * epsP q s = 2 * epsP p s := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (frame_eps_Z p.1 p.2 s.1 s.2)
  push_cast at h
  rw [sum_pair]
  simpa only [frameP, epsP] using h

theorem eps_eps_leftP (r s : Pair) : ∑ p, epsP p r * epsP p s = 2 * frameP r s := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (eps_eps_left_Z r.1 r.2 s.1 s.2)
  push_cast at h
  rw [sum_pair]
  simpa only [frameP, epsP] using h

/-- Contracting with the frame: `Σ_{pq} R_{pq} E_{pq} = Σ_{ab} (R_{abab} − R_{abba})`. -/
theorem contract_frameP (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ p, ∑ q, onPairs R p q * frameP p q = ∑ a, ∑ b, (R a b a b - R a b b a) := by
  rw [sum_pair]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [sum_pair]
  simp only [onPairs, frameP, frameZ]
  push_cast
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, ite_and]
  simp [Finset.sum_ite_eq]

theorem form_antisymm_diag (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ a b e f, R a b f e = -R a b e f) :
    ∑ a, ∑ b, (R a b a b - R a b b a) = 2 * scalarR R := by
  rw [scalarR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hR a b a b]
  ring

/-- **`R ∧ E = 2R`** for a curvature antisymmetric in its form pair. -/
theorem wedge_R_E (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ a b e f, R a b f e = -R a b e f) : wedge (onPairs R) frameP = 2 * scalarR R := by
  have h1 : ∀ p r q, ∑ s, epsP p r * onPairs R p q * frameP r s * epsP q s =
      epsP p r * onPairs R p q * (2 * epsP q r) := by
    intro p r q
    rw [← eps_frameP r q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have h2 : ∀ p, ∑ r, ∑ q, epsP p r * onPairs R p q * (2 * epsP q r) =
      ∑ q, onPairs R p q * (2 * (2 * frameP p q)) := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← eps_epsP p q, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have e : wedge (onPairs R) frameP = ∑ p, ∑ q, onPairs R p q * frameP p q := by
    rw [wedge]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e, contract_frameP, form_antisymm_diag R hR]

/-- **`E ∧ R = 2R`.** -/
theorem wedge_E_R (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ a b e f, R a b f e = -R a b e f) : wedge frameP (onPairs R) = 2 * scalarR R := by
  have h1 : ∀ p r, ∑ q, ∑ s, epsP p r * frameP p q * onPairs R r s * epsP q s =
      ∑ s, epsP p r * onPairs R r s * (2 * epsP p s) := by
    intro p r
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← frame_epsP p s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h2 : ∑ p, ∑ r, ∑ s, epsP p r * onPairs R r s * (2 * epsP p s) =
      ∑ r, ∑ s, onPairs R r s * (2 * (2 * frameP r s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← eps_eps_leftP r s, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have e : wedge frameP (onPairs R) = ∑ r, ∑ s, onPairs R r s * frameP r s := by
    rw [wedge]
    simp only [h1]
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, contract_frameP, form_antisymm_diag R hR]

/-- The frame as a four-index tensor. -/
def frame4 (a b e f : Fin 4) : ℝ := (frameZ a b e f : ℝ)

theorem onPairs_frame4 : onPairs frame4 = frameP := rfl

/-- **`E ∧ E = 24`.** -/
theorem wedge_E_E : wedge frameP frameP = 24 := by
  have hanti : ∀ a b e f, frame4 a b f e = -frame4 a b e f := by
    intro a b e f
    simp only [frame4]
    rw [frameZ_antisymm]
    push_cast
    ring
  have hw := wedge_R_E frame4 hanti
  rw [onPairs_frame4] at hw
  rw [hw, ← form_antisymm_diag frame4 hanti]
  have h := congrArg (fun z : ℤ => (z : ℝ)) frame_diag_Z
  push_cast at h
  simpa only [frame4] using h

/-- The pairing is bilinear: the expansion of `(X − tY) ∧ (X − tY)`. -/
theorem wedge_expand (X Y : Pair → Pair → ℝ) (t : ℝ) :
    wedge (fun p q => X p q - t * Y p q) (fun p q => X p q - t * Y p q) =
      wedge X X - t * (wedge X Y + wedge Y X) + t ^ 2 * wedge Y Y := by
  have hpt : ∀ p r q s, epsP p r * (X p q - t * Y p q) * (X r s - t * Y r s) * epsP q s =
      epsP p r * X p q * X r s * epsP q s -
        t * (epsP p r * X p q * Y r s * epsP q s + epsP p r * Y p q * X r s * epsP q s) +
        t ^ 2 * (epsP p r * Y p q * Y r s * epsP q s) := by
    intro p r q s
    ring
  simp only [wedge, hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The curvature identity at the last-step direction:** for every curvature `R` antisymmetric in its form pair,
`(R − E/ℓ²) ∧ (R − E/ℓ²) − R ∧ R = −(4/ℓ²)(R − 6/ℓ²)`, `R = Σ_{ab} R_{abab}`. -/
theorem curvature_identity (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ a b e f, R a b f e = -R a b e f) (ℓ : ℝ) :
    wedge (fun p q => onPairs R p q - frameP p q / ℓ ^ 2)
        (fun p q => onPairs R p q - frameP p q / ℓ ^ 2) - wedge (onPairs R) (onPairs R) =
      -(4 / ℓ ^ 2) * (scalarR R - 6 / ℓ ^ 2) := by
  have e : (fun p q => onPairs R p q - frameP p q / ℓ ^ 2) =
      (fun p q => onPairs R p q - 1 / ℓ ^ 2 * frameP p q) := by
    funext p q
    ring
  rw [e, wedge_expand, wedge_R_E R hR, wedge_E_R R hR, wedge_E_E]
  ring

/-- **`Λ = 3/ℓ²`:** the volume term `24/ℓ⁴` equals `(4/ℓ²)·2Λ` exactly when `Λ = 3/ℓ²`, so the
identity reads `−(4/ℓ²)(R − 2Λ)`. -/
theorem lambda_three (ℓ : ℝ) (hℓ : ℓ ≠ 0) (Λ : ℝ) :
    (24 / ℓ ^ 4 = (4 / ℓ ^ 2) * (2 * Λ)) ↔ Λ = 3 / ℓ ^ 2 := by
  have h2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  constructor
  · intro h
    field_simp at h
    field_simp
    nlinarith [h, sq_nonneg ℓ]
  · intro h
    rw [h]
    field_simp
    ring

end Comparison.WholePicture

end
