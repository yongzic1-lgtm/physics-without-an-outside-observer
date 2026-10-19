import Comparison.Article.FieldNumbers
import Comparison.Article.QLeptonsQuarks

/-!
# Each mass's pencil (Eq. 38)

`Article/FieldNumbers.lean` proves the generic pencil `K_X(ζ) = [[ζC_L, −A], [−B, ζC_R]]`: its zeros
are `±Ω_X`, `Ω_X² = AB/(C_LC_R)`, and a change of either end's description multiplies `AB` and
`C_LC_R` by one factor. A mass is the zero's vertex in the unit of the electron's one arc, `1/320`.

* `pencil_entries_iff`: **the entries of the pencil of a mass `Ω` are exactly the
  `(C_L, C_R, A, B)` with `AB = Ω² C_LC_R`**: fixed up to the change of description, nothing more;
* `mass_pencil`: **for every ratio `R > 0` the pencil `C_L = C_R = 1`, `A = B = R/320` has the zeros
  `±R/320`, and `Ω_X/Ω_e = R`**;
* `electron_pencil`, `proton_pencil`, `neutron_pencil`, `muon_pencil`, `tau_pencil`: **each mass's
  pencil, with its entries from its composition** (`qRp`, `qRn`, `qRmu`, `qRtau`, each bounded to the
  printed digits in `Article/QBase.lean`, `Article/QLeptonsQuarks.lean`).
-/

namespace Comparison.GroupsContinuumLaw

open Comparison.Article

/-- The electron's zero: one arc of the `320`. -/
noncomputable def omegaE : ℝ := 1 / 320

theorem omegaE_pos : 0 < omegaE := by unfold omegaE; norm_num

/-- **The pencil of a mass `Ω` is any `(C_L, C_R, A, B)` with `AB = Ω² C_LC_R`.** -/
theorem pencil_entries_iff (Ω CL CR A B : ℝ) (hC : CL * CR ≠ 0) :
    (pencil Ω CL CR A B).det = 0 ↔ A * B = Ω ^ 2 * (CL * CR) := by
  rw [pencil_det, sub_eq_zero, eq_comm]

/-- **The pencil of a mass of ratio `R`:** zeros `±R/320`, ratio `R`. -/
theorem mass_pencil (R : ℝ) (hR : 0 < R) :
    (∀ ζ : ℝ, (pencil ζ 1 1 (R * omegaE) (R * omegaE)).det = 0 ↔
      ζ = R * omegaE ∨ ζ = -(R * omegaE)) ∧
    (R * omegaE) / omegaE = R := by
  refine ⟨fun ζ => ?_, ?_⟩
  · rw [pencil_det, mul_one, mul_one, sub_eq_zero, ← sq, sq_eq_sq_iff_eq_or_eq_neg]
  · field_simp [omegaE_pos.ne']

theorem bnd_pos {x a b : ℝ} (h : Bnd x a b) (ha : 0 < a) : 0 < x := lt_of_lt_of_le ha h.1

/-- The electron: `R = 1`, the unit. -/
theorem electron_pencil :
    (∀ ζ : ℝ, (pencil ζ 1 1 (1 * omegaE) (1 * omegaE)).det = 0 ↔
      ζ = 1 * omegaE ∨ ζ = -(1 * omegaE)) ∧ (1 * omegaE) / omegaE = 1 :=
  mass_pencil 1 one_pos

/-- **The proton's pencil**, `R = m_p/m_e = 6M + C_h + (1/6)log(5/2) − a⁵ − ba⁶`. -/
theorem proton_pencil :
    (∀ ζ : ℝ, (pencil ζ 1 1 (qRp * omegaE) (qRp * omegaE)).det = 0 ↔
      ζ = qRp * omegaE ∨ ζ = -(qRp * omegaE)) ∧ (qRp * omegaE) / omegaE = qRp :=
  mass_pencil qRp (bnd_pos qRp_bnd (by norm_num))

/-- **The neutron's pencil**, `R = (m_p/m_e)(m_n/m_p)`. -/
theorem neutron_pencil :
    (∀ ζ : ℝ, (pencil ζ 1 1 (qRp * qRn * omegaE) (qRp * qRn * omegaE)).det = 0 ↔
      ζ = qRp * qRn * omegaE ∨ ζ = -(qRp * qRn * omegaE)) ∧
    (qRp * qRn * omegaE) / omegaE = qRp * qRn :=
  mass_pencil (qRp * qRn) (mul_pos (bnd_pos qRp_bnd (by norm_num)) (bnd_pos qRn_bnd (by norm_num)))

/-- **The muon's pencil**, `R = m_μ/m_e = 3⁵ e^{−9/56} M_Q(ν)^{1/6}`. -/
theorem muon_pencil :
    (∀ ζ : ℝ, (pencil ζ 1 1 (qRmu * omegaE) (qRmu * omegaE)).det = 0 ↔
      ζ = qRmu * omegaE ∨ ζ = -(qRmu * omegaE)) ∧ (qRmu * omegaE) / omegaE = qRmu :=
  mass_pencil qRmu (bnd_pos qRmu_bnd (by norm_num))

/-- **The tau's pencil**, `R = (m_μ/m_e)(m_τ/m_μ)`. -/
theorem tau_pencil :
    (∀ ζ : ℝ, (pencil ζ 1 1 (qRmu * qRtau * omegaE) (qRmu * qRtau * omegaE)).det = 0 ↔
      ζ = qRmu * qRtau * omegaE ∨ ζ = -(qRmu * qRtau * omegaE)) ∧
    (qRmu * qRtau * omegaE) / omegaE = qRmu * qRtau :=
  mass_pencil (qRmu * qRtau)
    (mul_pos (bnd_pos qRmu_bnd (by norm_num)) (bnd_pos qRtau_bnd (by norm_num)))

end Comparison.GroupsContinuumLaw
