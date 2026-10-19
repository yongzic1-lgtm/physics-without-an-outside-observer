import Comparison.Article.QKaon
import Comparison.Law.Composite

/-!
# The kaons (rows J08, J09; Propositions 197 and 198)

The light level `S_d` solves `6 m_p² Tr δ₁(R(R_ud S_d, S_d; 8/15)) = m_π⁰²` (Proposition 197,
`Law.light_level_equation`). Here:

* `deltaLevel_strictMono`: `δ₁` is strictly increasing; `eigenPlus_smul`, `eigenMinus_smul`: the level operator's
  eigenvalues scale with a common level, so the light level's shift is `δ₁(S μ₊) + δ₁(S μ₋)`, strictly increasing
  in `S`.
* `light_level_exists`, `light_level_unique`, `light_level_mem`: **the light level exists, is unique, and lies in
  `[sdLo, sdHi]`**, an interval of relative width `2·10⁻¹⁷` around `0.0118558163507453`.
* `rowJ08_digits`: **K⁰ `= m_p[6 Tr δ₁(R(S_d, pS_d; 8/15))]^{1/2}` lies within its printed digits
  `497.613584451` MeV** (Proposition 198's value); `rowJ09_digits`: **K± `= [6m_p² Tr δ₁(R(S_u, S_s; 8/15)) +
  (8/25)·6Δ_el]^{1/2}` within `493.665032668` MeV.**
-/

namespace Comparison.Article

open Real Comparison.Law

/-! ## `δ₁` and the eigenvalues of the level operator -/

theorem deltaLevel_eq (S : ℝ) :
    deltaLevel S = Real.log (4 * (2 / (3 + √(9 + 16 * Real.exp (-S))))) := rfl

theorem deltaLevel_strictMono : StrictMono deltaLevel := by
  intro a b hab
  rw [deltaLevel_eq, deltaLevel_eq]
  have h1 : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : √(9 + 16 * Real.exp (-b)) < √(9 + 16 * Real.exp (-a)) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have h3 : 0 < 3 + √(9 + 16 * Real.exp (-b)) := by positivity
  apply Real.log_lt_log (by positivity)
  have : 2 / (3 + √(9 + 16 * Real.exp (-a))) < 2 / (3 + √(9 + 16 * Real.exp (-b))) :=
    div_lt_div_of_pos_left (by norm_num) h3 (by linarith)
  linarith

theorem deltaLevel_continuous : Continuous deltaLevel := by
  have h : ∀ S : ℝ, 0 < 3 + √(9 + 16 * Real.exp (-S)) := fun S => by positivity
  have hc : Continuous fun S : ℝ => 4 * (2 / (3 + √(9 + 16 * Real.exp (-S)))) := by
    refine continuous_const.mul (continuous_const.div ?_ (fun S => (h S).ne'))
    exact continuous_const.add (Real.continuous_sqrt.comp (continuous_const.add
      (continuous_const.mul (Real.continuous_exp.comp continuous_neg))))
  exact hc.log (fun S => by have := h S; positivity)

theorem discR_smul (a b c x : ℝ) (hx : 0 ≤ x) : discR (a * x) (b * x) c = x * discR a b c := by
  rw [discR, discR, show (a * x - b * x) ^ 2 + 4 * c * (a * x) * (b * x) =
    x ^ 2 * ((a - b) ^ 2 + 4 * c * a * b) by ring, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx]

theorem eigenPlus_smul (a b c x : ℝ) (hx : 0 ≤ x) :
    eigenPlus (a * x) (b * x) c = x * eigenPlus a b c := by
  rw [eigenPlus, eigenPlus, discR_smul a b c x hx]
  ring

theorem eigenMinus_smul (a b c x : ℝ) (hx : 0 ≤ x) :
    eigenMinus (a * x) (b * x) c = x * eigenMinus a b c := by
  rw [eigenMinus, eigenMinus, discR_smul a b c x hx]
  ring

theorem muP_eq : eigenPlus (17 / 37) 1 (8 / 15) = qMuP := by
  rw [eigenPlus, discR, qMuP]
  norm_num

theorem muM_eq : eigenMinus (17 / 37) 1 (8 / 15) = qMuM := by
  rw [eigenMinus, discR, qMuM]
  norm_num

theorem muM_pos : 0 < qMuM := lt_of_lt_of_le (by norm_num) qMuM_bnd.1
theorem muP_pos : 0 < qMuP := lt_of_lt_of_le (by norm_num) qMuP_bnd.1

/-- **The light level's shift** `Tr δ₁(R(R_ud S, S; 8/15)) = δ₁(S μ₊) + δ₁(S μ₋)`. -/
theorem lightShift_eq (S : ℝ) (hS : 0 ≤ S) :
    compositeDelta ((17 / 37) * S) S (8 / 15) = deltaLevel (S * qMuP) + deltaLevel (S * qMuM) := by
  have e : compositeDelta ((17 / 37) * S) S (8 / 15) = compositeDelta ((17 / 37) * S) (1 * S) (8 / 15) := by
    rw [one_mul]
  rw [e, compositeDelta, eigenPlus_smul _ _ _ _ hS, eigenMinus_smul _ _ _ _ hS, muP_eq, muM_eq,
    mul_comm S qMuP, mul_comm S qMuM]

theorem lightShift_strictMonoOn :
    StrictMonoOn (fun S => deltaLevel (S * qMuP) + deltaLevel (S * qMuM)) (Set.Ici 0) := by
  intro a _ b _ hab
  have h1 := deltaLevel_strictMono (mul_lt_mul_of_pos_right hab muP_pos)
  have h2 := deltaLevel_strictMono (mul_lt_mul_of_pos_right hab muM_pos)
  simp only
  linarith

theorem light_at_l : deltaLevel (sdLo * qMuP) + deltaLevel (sdLo * qMuM) < qTarget := by
  have h := light_level_at_l
  have e : sdLo = (59279081753726513400927 : ℝ) / 5000000000000000000000000 := by
    rw [sdLo]; norm_num
  rw [e, deltaLevel_eq, deltaLevel_eq]
  exact lt_of_le_of_lt h.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)

theorem light_at_u : qTarget < deltaLevel (sdHi * qMuP) + deltaLevel (sdHi * qMuM) := by
  have h := light_level_at_u
  have e : sdHi = (118558163507453029173019 : ℝ) / 10000000000000000000000000 := by
    rw [sdHi]; norm_num
  rw [e, deltaLevel_eq, deltaLevel_eq]
  exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) h.1)

theorem target_eq : qTarget = qPi0 ^ 2 / (6 * qMp ^ 2) := rfl

theorem qMp_pos : 0 < qMp := lt_of_lt_of_le (by norm_num) qMp_bnd.1

/-- The light level's equation at the proton and the neutral pion, as a value of the shift. -/
theorem light_level_iff (S : ℝ) (hS : 0 ≤ S) :
    light_level_equation S qMp (qPi0 ^ 2) ↔ deltaLevel (S * qMuP) + deltaLevel (S * qMuM) = qTarget := by
  rw [light_level_equation, lightShift_eq S hS, target_eq]
  have hm : 0 < 6 * qMp ^ 2 := by have := qMp_pos; positivity
  constructor
  · intro h
    rw [eq_div_iff hm.ne']
    linarith
  · intro h
    have hp := qMp_pos.ne'
    rw [h]
    field_simp

/-- **The light level exists** in `[sdLo, sdHi]` (Proposition 197). -/
theorem light_level_exists : ∃ S ∈ Set.Icc sdLo sdHi, light_level_equation S qMp (qPi0 ^ 2) := by
  have hlo : (0 : ℝ) ≤ sdLo := by rw [sdLo]; norm_num
  have hle : sdLo ≤ sdHi := by rw [sdLo, sdHi]; norm_num
  have hcont : ContinuousOn (fun S => deltaLevel (S * qMuP) + deltaLevel (S * qMuM)) (Set.Icc sdLo sdHi) :=
    ((deltaLevel_continuous.comp (continuous_id.mul continuous_const)).add
      (deltaLevel_continuous.comp (continuous_id.mul continuous_const))).continuousOn
  obtain ⟨S, hS, hval⟩ := intermediate_value_Icc hle hcont ⟨light_at_l.le, light_at_u.le⟩
  exact ⟨S, hS, (light_level_iff S (hlo.trans hS.1)).mpr hval⟩

/-- **The light level lies in `[sdLo, sdHi]`.** -/
theorem light_level_mem (S : ℝ) (hS : 0 ≤ S) (h : light_level_equation S qMp (qPi0 ^ 2)) :
    Bnd S sdLo sdHi := by
  rw [light_level_iff S hS] at h
  have hlo : (0 : ℝ) ≤ sdLo := by rw [sdLo]; norm_num
  have hhi : (0 : ℝ) ≤ sdHi := by rw [sdHi]; norm_num
  constructor
  · by_contra hc
    have hc' := lt_of_not_ge hc
    have := lightShift_strictMonoOn hS hlo hc'
    simp only at this
    linarith [light_at_l]
  · by_contra hc
    have hc' := lt_of_not_ge hc
    have := lightShift_strictMonoOn hhi hS hc'
    simp only at this
    linarith [light_at_u]

/-- **The light level is unique.** -/
theorem light_level_unique (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (h1 : light_level_equation S qMp (qPi0 ^ 2))
    (h2 : light_level_equation T qMp (qPi0 ^ 2)) : S = T := by
  rw [light_level_iff S hS] at h1
  rw [light_level_iff T hT] at h2
  have e : (fun S => deltaLevel (S * qMuP) + deltaLevel (S * qMuM)) S =
      (fun S => deltaLevel (S * qMuP) + deltaLevel (S * qMuM)) T := by
    show deltaLevel (S * qMuP) + deltaLevel (S * qMuM) = deltaLevel (T * qMuP) + deltaLevel (T * qMuM)
    rw [h1, h2]
  exact lightShift_strictMonoOn.injOn hS hT e

/-! ## K⁰ and K± -/

theorem massOp_p : massOp .symmetric sPlaneSinglet = qP := by
  rw [row_p_quark, clockMQ_minus, qP,
    show (3 : ℝ) ^ (5 : ℝ) = 243 by rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]

theorem nuP_eq : eigenPlus 1 qP (8 / 15) = qNuP := by
  rw [eigenPlus, discR, qNuP, qDiscP,
    show (1 - qP) ^ 2 + 4 * (8 / 15) * 1 * qP = (qP - 1) ^ 2 + 32 / 15 * qP by ring]

theorem nuM_eq : eigenMinus 1 qP (8 / 15) = qNuM := by
  rw [eigenMinus, discR, qNuM, qDiscP,
    show (1 - qP) ^ 2 + 4 * (8 / 15) * 1 * qP = (qP - 1) ^ 2 + 32 / 15 * qP by ring]

theorem kapP_eq : eigenPlus (17 / 37) qP (8 / 15) = qKapP := by
  rw [eigenPlus, discR, qKapP, qDiscK,
    show (17 / 37 - qP) ^ 2 + 4 * (8 / 15) * (17 / 37) * qP = (qP - 17 / 37) ^ 2 + 544 / 555 * qP by ring]

theorem kapM_eq : eigenMinus (17 / 37) qP (8 / 15) = qKapM := by
  rw [eigenMinus, discR, qKapM, qDiscK,
    show (17 / 37 - qP) ^ 2 + 4 * (8 / 15) * (17 / 37) * qP = (qP - 17 / 37) ^ 2 + 544 / 555 * qP by ring]

/-- **K⁰ at the light level:** `m = (rowK0sq S_d m_p)^{1/2} = m_p[6 Tr δ₁(R(S_d, pS_d; 8/15))]^{1/2}`. -/
noncomputable def rowJ08Of (S : ℝ) : ℝ := √(rowK0sq S qMp)

theorem rowJ08Of_eq (S : ℝ) (hS : 0 ≤ S) :
    rowJ08Of S = qMp * √(6 * (deltaLevel (S * qNuP) + deltaLevel (S * qNuM))) := by
  have e : compositeDelta S (massOp .symmetric sPlaneSinglet * S) (8 / 15) =
      deltaLevel (S * qNuP) + deltaLevel (S * qNuM) := by
    rw [massOp_p, show compositeDelta S (qP * S) (8 / 15) = compositeDelta (1 * S) (qP * S) (8 / 15) by
      rw [one_mul], compositeDelta, eigenPlus_smul _ _ _ _ hS, eigenMinus_smul _ _ _ _ hS, nuP_eq, nuM_eq,
      mul_comm S qNuP, mul_comm S qNuM]
  rw [rowJ08Of, rowK0sq, e, show 6 * qMp ^ 2 * (deltaLevel (S * qNuP) + deltaLevel (S * qNuM)) =
    qMp ^ 2 * (6 * (deltaLevel (S * qNuP) + deltaLevel (S * qNuM))) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq qMp_pos.le]

/-- **Row J08, K⁰, to its printed digits `497.613584451` MeV**, at the light level of Proposition 197. -/
theorem rowJ08_digits (S : ℝ) (hS : 0 ≤ S) (h : light_level_equation S qMp (qPi0 ^ 2)) :
    497.6135844505 < rowJ08Of S ∧ rowJ08Of S < 497.6135844515 := by
  have hb := J08_of_root S (by have := light_level_mem S hS h; rw [sdLo, sdHi] at this; exact this)
  rw [rowJ08Of_eq S hS]
  simp only [deltaLevel_eq]
  exact hb.strict (by norm_num) (by norm_num)

/-- **K± at the light level:** `m² = 6m_p² Tr δ₁(R(R_ud S_d, pS_d; 8/15)) + (8/25)·6Δ_el`. -/
noncomputable def rowJ09Of (S : ℝ) : ℝ :=
  √(6 * qMp ^ 2 * compositeDelta ((17 / 37) * S) (massOp .symmetric sPlaneSinglet * S) (8 / 15) + 8 / 25 * 6 * qElec)

theorem rowJ09Of_eq (S : ℝ) (hS : 0 ≤ S) :
    rowJ09Of S = √(6 * qMp ^ 2 * (deltaLevel (S * qKapP) + deltaLevel (S * qKapM)) + 48 / 25 * qElec) := by
  rw [rowJ09Of, massOp_p, compositeDelta, eigenPlus_smul _ _ _ _ hS, eigenMinus_smul _ _ _ _ hS, kapP_eq,
    kapM_eq, mul_comm S qKapP, mul_comm S qKapM]
  norm_num

/-- **Row J09, K±, to its printed digits `493.665032668` MeV.** -/
theorem rowJ09_digits (S : ℝ) (hS : 0 ≤ S) (h : light_level_equation S qMp (qPi0 ^ 2)) :
    493.6650326675 < rowJ09Of S ∧ rowJ09Of S < 493.6650326685 := by
  have hb := J09_of_root S (by have := light_level_mem S hS h; rw [sdLo, sdHi] at this; exact this)
  rw [rowJ09Of_eq S hS]
  simp only [deltaLevel_eq]
  exact hb.strict (by norm_num) (by norm_num)

end Comparison.Article
