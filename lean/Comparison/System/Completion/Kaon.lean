import Comparison.System.Completion.QK0
import Comparison.System.Completion.Composition

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 10: `K⁰` at every coupling (SI Prop. 198, complete)

The SI's diagnostics of `K⁰` refit the light level at each coupling `c` (the charged pion's
strong part at the same `c`: Prop. 197's equation with `8/15` replaced by `c`) and evaluate `K⁰` there: the line side
alone (`c = 0`), the meeting side alone (`c = 1`), and the asks `c = 0.5229, 0.5359, 0.5490`; at `c = 8/15` with the
book's light level, `K⁰` at `p = 19.961420, 19.960252, 19.962588` and at `p(1 + 10⁻⁵)`; and the shift's form. The
intervals are `Completion/QK0.lean`.
-/

namespace Comparison.System.Completion.Comp

open Real Comparison Comparison.Law Comparison.Article

/-- A strictly increasing continuous `f` below `T` at `l` and above at `u`: a root of `f = T` in `[l, u]`, and every
root lies there. -/
theorem root_between (f : ℝ → ℝ) (hf : StrictMono f) (hc : Continuous f) (l u T : ℝ) (hlu : l ≤ u)
    (hL : f l < T) (hU : T < f u) : (∃ S ∈ Set.Icc l u, f S = T) ∧ (∀ S, f S = T → S ∈ Set.Icc l u) := by
  refine ⟨?_, fun S hS => ⟨?_, ?_⟩⟩
  · obtain ⟨S, hS, hval⟩ := intermediate_value_Icc hlu hc.continuousOn ⟨hL.le, hU.le⟩
    exact ⟨S, hS, hval⟩
  · by_contra h
    push_neg at h
    have := hf h
    linarith
  · by_contra h
    push_neg at h
    have := hf h
    linarith

theorem two_levels_mono (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    StrictMono (fun S : ℝ => deltaLevel (S * x) + deltaLevel (S * y)) := by
  intro a b hab
  have h1 := Article.deltaLevel_strictMono (mul_lt_mul_of_pos_right hab hx)
  have h2 := Article.deltaLevel_strictMono.monotone (mul_le_mul_of_nonneg_right hab.le hy)
  simp only
  linarith

theorem two_levels_cont (x y : ℝ) : Continuous (fun S : ℝ => deltaLevel (S * x) + deltaLevel (S * y)) :=
  (Article.deltaLevel_continuous.comp (continuous_id.mul continuous_const)).add
    (Article.deltaLevel_continuous.comp (continuous_id.mul continuous_const))

/-- `Tr δ₁(R(aS, bS; c)) = δ₁(Sλ₊(a, b, c)) + δ₁(Sλ₋(a, b, c))` for `S ≥ 0`. -/
theorem compositeDelta_scale (a b c S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (a * S) (b * S) c = deltaLevel (S * eigenPlus a b c) + deltaLevel (S * eigenMinus a b c) := by
  rw [compositeDelta, eigenPlus_smul a b c S hS, eigenMinus_smul a b c S hS]

theorem shift_light (c S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (17 / 37 * S) S c =
      deltaLevel (S * eigenPlus (17 / 37) 1 c) + deltaLevel (S * eigenMinus (17 / 37) 1 c) := by
  have e : compositeDelta (17 / 37 * S) S c = compositeDelta (17 / 37 * S) (1 * S) c := by rw [one_mul]
  rw [e, compositeDelta_scale _ _ _ _ hS]

theorem shift_kaon (b c S : ℝ) (hS : 0 ≤ S) :
    compositeDelta S (b * S) c = deltaLevel (S * eigenPlus 1 b c) + deltaLevel (S * eigenMinus 1 b c) := by
  have e : compositeDelta S (b * S) c = compositeDelta (1 * S) (b * S) c := by rw [one_mul]
  rw [e, compositeDelta_scale _ _ _ _ hS]

/-- The pion's equation at the coupling `c` as a value of the shift. -/
theorem pion_iff (S c : ℝ) :
    6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S c = qPi0 ^ 2 ↔ compositeDelta (17 / 37 * S) S c = qTarget := by
  rw [target_eq]
  have hm : 0 < 6 * qMp ^ 2 := by have := qMp_pos; positivity
  constructor
  · intro h
    rw [eq_div_iff hm.ne']
    linarith
  · intro h
    rw [h]
    have hp := qMp_pos.ne'
    field_simp

/-- From a value's interval to its standard deviations. -/
theorem widths_of (m lo hi wlo whi : ℝ) (h : Bnd m lo hi) (h3 : wlo * 0.013 + 497.611 < lo)
    (h4 : hi < whi * 0.013 + 497.611) : wlo < (m - 497.611) / 0.013 ∧ (m - 497.611) / 0.013 < whi := by
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem lMuP_a_eq : eigenPlus (17 / 37) 1 (5229 / 10000) = QK.lMuP_a := by
  rw [eigenPlus, discR, QK.lMuP_a]
  norm_num

theorem lMuM_a_eq : eigenMinus (17 / 37) 1 (5229 / 10000) = QK.lMuM_a := by
  rw [eigenMinus, discR, QK.lMuM_a]
  norm_num

theorem kNuP_a_eq : eigenPlus 1 qP (5229 / 10000) = QK.kNuP_a := by
  rw [eigenPlus, discR, QK.kNuP_a, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem kNuM_a_eq : eigenMinus 1 qP (5229 / 10000) = QK.kNuM_a := by
  rw [eigenMinus, discR, QK.kNuM_a, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem lMuP_b_eq : eigenPlus (17 / 37) 1 (5359 / 10000) = QK.lMuP_b := by
  rw [eigenPlus, discR, QK.lMuP_b]
  norm_num

theorem lMuM_b_eq : eigenMinus (17 / 37) 1 (5359 / 10000) = QK.lMuM_b := by
  rw [eigenMinus, discR, QK.lMuM_b]
  norm_num

theorem kNuP_b_eq : eigenPlus 1 qP (5359 / 10000) = QK.kNuP_b := by
  rw [eigenPlus, discR, QK.kNuP_b, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem kNuM_b_eq : eigenMinus 1 qP (5359 / 10000) = QK.kNuM_b := by
  rw [eigenMinus, discR, QK.kNuM_b, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem lMuP_d_eq : eigenPlus (17 / 37) 1 (549 / 1000) = QK.lMuP_d := by
  rw [eigenPlus, discR, QK.lMuP_d]
  norm_num

theorem lMuM_d_eq : eigenMinus (17 / 37) 1 (549 / 1000) = QK.lMuM_d := by
  rw [eigenMinus, discR, QK.lMuM_d]
  norm_num

theorem kNuP_d_eq : eigenPlus 1 qP (549 / 1000) = QK.kNuP_d := by
  rw [eigenPlus, discR, QK.kNuP_d, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem kNuM_d_eq : eigenMinus 1 qP (549 / 1000) = QK.kNuM_d := by
  rw [eigenMinus, discR, QK.kNuM_d, show ((1 : ℝ) - qP) ^ 2 = (qP - 1) ^ 2 by ring]

theorem pNuP_m_eq : eigenPlus 1 (19961420 / 1000000) (8 / 15) = QK.pNuP_m := by
  rw [eigenPlus, discR, QK.pNuP_m]
  norm_num

theorem pNuM_m_eq : eigenMinus 1 (19961420 / 1000000) (8 / 15) = QK.pNuM_m := by
  rw [eigenMinus, discR, QK.pNuM_m]
  norm_num

theorem pNuP_lo_eq : eigenPlus 1 (19960252 / 1000000) (8 / 15) = QK.pNuP_lo := by
  rw [eigenPlus, discR, QK.pNuP_lo]
  norm_num

theorem pNuM_lo_eq : eigenMinus 1 (19960252 / 1000000) (8 / 15) = QK.pNuM_lo := by
  rw [eigenMinus, discR, QK.pNuM_lo]
  norm_num

theorem pNuP_hi_eq : eigenPlus 1 (19962588 / 1000000) (8 / 15) = QK.pNuP_hi := by
  rw [eigenPlus, discR, QK.pNuP_hi]
  norm_num

theorem pNuM_hi_eq : eigenMinus 1 (19962588 / 1000000) (8 / 15) = QK.pNuM_hi := by
  rw [eigenMinus, discR, QK.pNuM_hi]
  norm_num

theorem sNuP_eq : eigenPlus 1 (qP * (100001 / 100000)) (8 / 15) = QK.sNuP := by
  rw [eigenPlus, discR, QK.sNuP, show ((1 : ℝ) - qP * (100001 / 100000)) ^ 2 = (qP * (100001 / 100000) - 1) ^ 2 by ring]

theorem sNuM_eq : eigenMinus 1 (qP * (100001 / 100000)) (8 / 15) = QK.sNuM := by
  rw [eigenMinus, discR, QK.sNuM, show ((1 : ℝ) - qP * (100001 / 100000)) ^ 2 = (qP * (100001 / 100000) - 1) ^ 2 by ring]

theorem root_0 :
    (∃ S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0, (fun S : ℝ => deltaLevel (17 / 37 * S) + deltaLevel S) S = qTarget) ∧
    (∀ S, (fun S : ℝ => deltaLevel (17 / 37 * S) + deltaLevel S) S = qTarget → S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0) := by
  refine root_between (fun S : ℝ => deltaLevel (17 / 37 * S) + deltaLevel S) (by
      intro x y hxy
      have h1 := Article.deltaLevel_strictMono (show 17 / 37 * x < 17 / 37 * y by linarith)
      have h2 := Article.deltaLevel_strictMono hxy
      simp only
      linarith) ((Article.deltaLevel_continuous.comp (continuous_const.mul continuous_id)).add Article.deltaLevel_continuous) QK.sdLo_0 QK.sdHi_0 qTarget
    (by rw [QK.sdLo_0, QK.sdHi_0]; norm_num) ?_ ?_
  · have hL := QK.level_at_l_0
    have e : QK.sdLo_0 = ((11844438616809865284203 : ℝ) / 1000000000000000000000000) := by rw [QK.sdLo_0]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt hL.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)
  · have hU := QK.level_at_u_0
    have e : QK.sdHi_0 = ((118444386168098655210919 : ℝ) / 10000000000000000000000000) := by rw [QK.sdHi_0]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) hU.1)

theorem root_1 :
    (∃ S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1, (fun S : ℝ => deltaLevel (17 / 37 * S + S)) S = qTarget) ∧
    (∀ S, (fun S : ℝ => deltaLevel (17 / 37 * S + S)) S = qTarget → S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1) := by
  refine root_between (fun S : ℝ => deltaLevel (17 / 37 * S + S)) (by
      intro x y hxy
      have h1 := Article.deltaLevel_strictMono (show 17 / 37 * x + x < 17 / 37 * y + y by linarith)
      simpa using h1) (Article.deltaLevel_continuous.comp ((continuous_const.mul continuous_id).add continuous_id)) QK.sdLo_1 QK.sdHi_1 qTarget
    (by rw [QK.sdLo_1, QK.sdHi_1]; norm_num) ?_ ?_
  · have hL := QK.level_at_l_1
    have e : QK.sdLo_1 = ((11865807857773821551061 : ℝ) / 1000000000000000000000000) := by rw [QK.sdLo_1]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt hL.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)
  · have hU := QK.level_at_u_1
    have e : QK.sdHi_1 = ((118658078577738217883773 : ℝ) / 10000000000000000000000000) := by rw [QK.sdHi_1]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) hU.1)

theorem root_a :
    (∃ S ∈ Set.Icc QK.sdLo_a QK.sdHi_a, (fun S : ℝ => deltaLevel (S * QK.lMuP_a) + deltaLevel (S * QK.lMuM_a)) S = qTarget) ∧
    (∀ S, (fun S : ℝ => deltaLevel (S * QK.lMuP_a) + deltaLevel (S * QK.lMuM_a)) S = qTarget → S ∈ Set.Icc QK.sdLo_a QK.sdHi_a) := by
  refine root_between (fun S : ℝ => deltaLevel (S * QK.lMuP_a) + deltaLevel (S * QK.lMuM_a)) (two_levels_mono _ _ (lt_of_lt_of_le (by norm_num) QK.lMuP_a_bnd.1) (le_trans (by norm_num) QK.lMuM_a_bnd.1)) (two_levels_cont _ _) QK.sdLo_a QK.sdHi_a qTarget
    (by rw [QK.sdLo_a, QK.sdHi_a]; norm_num) ?_ ?_
  · have hL := QK.level_at_l_a
    have e : QK.sdLo_a = ((118555933539901081908017 : ℝ) / 10000000000000000000000000) := by rw [QK.sdLo_a]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt hL.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)
  · have hU := QK.level_at_u_a
    have e : QK.sdHi_a = ((3704872923121908883723 : ℝ) / 312500000000000000000000) := by rw [QK.sdHi_a]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) hU.1)

theorem root_b :
    (∃ S ∈ Set.Icc QK.sdLo_b QK.sdHi_b, (fun S : ℝ => deltaLevel (S * QK.lMuP_b) + deltaLevel (S * QK.lMuM_b)) S = qTarget) ∧
    (∀ S, (fun S : ℝ => deltaLevel (S * QK.lMuP_b) + deltaLevel (S * QK.lMuM_b)) S = qTarget → S ∈ Set.Icc QK.sdLo_b QK.sdHi_b) := by
  refine root_between (fun S : ℝ => deltaLevel (S * QK.lMuP_b) + deltaLevel (S * QK.lMuM_b)) (two_levels_mono _ _ (lt_of_lt_of_le (by norm_num) QK.lMuP_b_bnd.1) (le_trans (by norm_num) QK.lMuM_b_bnd.1)) (two_levels_cont _ _) QK.sdLo_b QK.sdHi_b qTarget
    (by rw [QK.sdLo_b, QK.sdHi_b]; norm_num) ?_ ?_
  · have hL := QK.level_at_l_b
    have e : QK.sdLo_b = ((118558712119459213479697 : ℝ) / 10000000000000000000000000) := by rw [QK.sdLo_b]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt hL.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)
  · have hU := QK.level_at_u_b
    have e : QK.sdHi_b = ((14819839014932401981359 : ℝ) / 1250000000000000000000000) := by rw [QK.sdHi_b]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) hU.1)

theorem root_d :
    (∃ S ∈ Set.Icc QK.sdLo_d QK.sdHi_d, (fun S : ℝ => deltaLevel (S * QK.lMuP_d) + deltaLevel (S * QK.lMuM_d)) S = qTarget) ∧
    (∀ S, (fun S : ℝ => deltaLevel (S * QK.lMuP_d) + deltaLevel (S * QK.lMuM_d)) S = qTarget → S ∈ Set.Icc QK.sdLo_d QK.sdHi_d) := by
  refine root_between (fun S : ℝ => deltaLevel (S * QK.lMuP_d) + deltaLevel (S * QK.lMuM_d)) (two_levels_mono _ _ (lt_of_lt_of_le (by norm_num) QK.lMuP_d_bnd.1) (le_trans (by norm_num) QK.lMuM_d_bnd.1)) (two_levels_cont _ _) QK.sdLo_d QK.sdHi_d qTarget
    (by rw [QK.sdLo_d, QK.sdHi_d]; norm_num) ?_ ?_
  · have hL := QK.level_at_l_d
    have e : QK.sdLo_d = ((118561512336478045433937 : ℝ) / 10000000000000000000000000) := by rw [QK.sdLo_d]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt hL.2 (lt_of_lt_of_le (by norm_num) qTarget_bnd.1)
  · have hU := QK.level_at_u_d
    have e : QK.sdHi_d = ((7410094521029877987823 : ℝ) / 625000000000000000000000) := by rw [QK.sdHi_d]; norm_num
    rw [e]
    simp only [Article.deltaLevel_eq]
    exact lt_of_le_of_lt qTarget_bnd.2 (lt_of_lt_of_le (by norm_num) hU.1)

theorem light_0 (S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (17 / 37 * S) S 0 = deltaLevel (17 / 37 * S) + deltaLevel S :=
  (composite_ends _ _ (mul_nonneg (by norm_num) hS) hS).1

theorem light_1 (S : ℝ) (hS : 0 ≤ S) : compositeDelta (17 / 37 * S) S 1 = deltaLevel (17 / 37 * S + S) :=
  (composite_ends _ _ (mul_nonneg (by norm_num) hS) hS).2

theorem light_a (S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (17 / 37 * S) S (5229 / 10000) = deltaLevel (S * QK.lMuP_a) + deltaLevel (S * QK.lMuM_a) := by
  rw [shift_light _ _ hS, lMuP_a_eq, lMuM_a_eq]

theorem light_b (S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (17 / 37 * S) S (5359 / 10000) = deltaLevel (S * QK.lMuP_b) + deltaLevel (S * QK.lMuM_b) := by
  rw [shift_light _ _ hS, lMuP_b_eq, lMuM_b_eq]

theorem light_d (S : ℝ) (hS : 0 ≤ S) :
    compositeDelta (17 / 37 * S) S (549 / 1000) = deltaLevel (S * QK.lMuP_d) + deltaLevel (S * QK.lMuM_d) := by
  rw [shift_light _ _ hS, lMuP_d_eq, lMuM_d_eq]

theorem k0_0 (S : ℝ) (hS : S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0) :
    Bnd (qMp * √(6 * compositeDelta S (qP * S) 0)) (4.9814340974309039528024956e2 : ℝ) (4.981434097430903999796209e2 : ℝ) := by
  have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_0]; norm_num) hS.1
  have hq : 0 ≤ qP * S := mul_nonneg (le_trans (by norm_num) qP_bnd.1) hS0
  rw [(composite_ends _ _ hS0 hq).1, mul_comm qP S, Article.deltaLevel_eq, Article.deltaLevel_eq]
  exact QK.K0_at_0 S hS

theorem k0_1 (S : ℝ) (hS : S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1) :
    Bnd (qMp * √(6 * compositeDelta S (qP * S) 1)) (4.9714789411441409859192647e2 : ℝ) (4.9714789411441410325168285e2 : ℝ) := by
  have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_1]; norm_num) hS.1
  have hq : 0 ≤ qP * S := mul_nonneg (le_trans (by norm_num) qP_bnd.1) hS0
  rw [(composite_ends _ _ hS0 hq).2, Article.deltaLevel_eq]
  exact QK.K0_at_1 S hS

theorem k0_a (S : ℝ) (hS : S ∈ Set.Icc QK.sdLo_a QK.sdHi_a) :
    Bnd (qMp * √(6 * compositeDelta S (qP * S) (5229 / 10000))) (4.9762397356531523935133976e2 : ℝ) (4.9762397356531524403004524e2 : ℝ) := by
  have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_a]; norm_num) hS.1
  rw [shift_kaon _ _ _ hS0, kNuP_a_eq, kNuM_a_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
  exact QK.K0_at_a S hS

theorem k0_b (S : ℝ) (hS : S ∈ Set.Icc QK.sdLo_b QK.sdHi_b) :
    Bnd (qMp * √(6 * compositeDelta S (qP * S) (5359 / 10000))) (4.9761102851270398779058558e2 : ℝ) (4.9761102851270399246877651e2 : ℝ) := by
  have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_b]; norm_num) hS.1
  rw [shift_kaon _ _ _ hS0, kNuP_b_eq, kNuM_b_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
  exact QK.K0_at_b S hS

theorem k0_d (S : ℝ) (hS : S ∈ Set.Icc QK.sdLo_d QK.sdHi_d) :
    Bnd (qMp * √(6 * compositeDelta S (qP * S) (549 / 1000))) (4.9759798234853775616370368e2 : ℝ) (4.975979823485377608413761e2 : ℝ) := by
  have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_d]; norm_num) hS.1
  rw [shift_kaon _ _ _ hS0, kNuP_d_eq, kNuM_d_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
  exact QK.K0_at_d S hS

end Comparison.System.Completion.Comp

namespace Comparison.System

open Real Comparison Comparison.Law Comparison.Article Comparison.System.Completion

/-- **Proposition 198, `K⁰` at every coupling.** With the light level refitted at each coupling `c`
(`6m_p²Tr δ₁(R(R_udS, S; c)) = m_π⁰²`: a nonnegative root exists and every nonnegative root lies in a stated interval
of relative width `2·10⁻¹⁷`) and `K⁰` evaluated at the same `c`, `m(c) = m_p(6Tr δ₁(R(S, pS; c)))^{1/2}`: the line side
alone (`c = 0`) `498.1434 MeV`, `+40.95` standard deviations of `497.611(13)` (PDG, outside input); the meeting side alone (`c = 1`)
`497.1479 MeV`, `−35.62`; the measured `K⁰` asks `c = 0.5359` (within `0.005` standard deviations) between `0.5229` (`+1.00`) and
`0.5490` (`−1.00`); at `c = 8/15` with the book's light level it asks `p = 19.961420` (within `0.005` standard deviations) between
`19.960252` (`−1.00`) and `19.962588` (`+1.00`), with `0.1709` standard deviations per `10⁻⁵` of `p`; the shift is
`Tr δ₁(R) = δ₁(S_s) + S_d[(1 − c)/5 + cδ₁′(S_s)] − (6/125)S_d² + 6.6·10⁻⁸`, `δ₁′(S_s) = f₁(e^{δ₁(S_s)}) = 0.177461`. -/
theorem Completion.Comp.kaon_every_coupling :
    ((∃ S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0, 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S 0 = qPi0 ^ 2) ∧
      ∀ S, 0 ≤ S → 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S 0 = qPi0 ^ 2 →
        ((498.14335 : ℝ) < qMp * √(6 * compositeDelta S (qP * S) 0) ∧ qMp * √(6 * compositeDelta S (qP * S) 0) < 498.14345) ∧
        ((40.945 : ℝ) < (qMp * √(6 * compositeDelta S (qP * S) 0) - 497.611) / 0.013 ∧
          (qMp * √(6 * compositeDelta S (qP * S) 0) - 497.611) / 0.013 < 40.955)) ∧
    ((∃ S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1, 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S 1 = qPi0 ^ 2) ∧
      ∀ S, 0 ≤ S → 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S 1 = qPi0 ^ 2 →
        ((497.14785 : ℝ) < qMp * √(6 * compositeDelta S (qP * S) 1) ∧ qMp * √(6 * compositeDelta S (qP * S) 1) < 497.14795) ∧
        ((-35.625 : ℝ) < (qMp * √(6 * compositeDelta S (qP * S) 1) - 497.611) / 0.013 ∧
          (qMp * √(6 * compositeDelta S (qP * S) 1) - 497.611) / 0.013 < -35.615)) ∧
    ((∃ S ∈ Set.Icc QK.sdLo_b QK.sdHi_b, 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (5359 / 10000) = qPi0 ^ 2) ∧
      ∀ S, 0 ≤ S → 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (5359 / 10000) = qPi0 ^ 2 →
        (-0.005 : ℝ) < (qMp * √(6 * compositeDelta S (qP * S) (5359 / 10000)) - 497.611) / 0.013 ∧
          (qMp * √(6 * compositeDelta S (qP * S) (5359 / 10000)) - 497.611) / 0.013 < 0.005) ∧
    ((∃ S ∈ Set.Icc QK.sdLo_a QK.sdHi_a, 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (5229 / 10000) = qPi0 ^ 2) ∧
      ∀ S, 0 ≤ S → 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (5229 / 10000) = qPi0 ^ 2 →
        (0.995 : ℝ) < (qMp * √(6 * compositeDelta S (qP * S) (5229 / 10000)) - 497.611) / 0.013 ∧
          (qMp * √(6 * compositeDelta S (qP * S) (5229 / 10000)) - 497.611) / 0.013 < 1.005) ∧
    ((∃ S ∈ Set.Icc QK.sdLo_d QK.sdHi_d, 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (549 / 1000) = qPi0 ^ 2) ∧
      ∀ S, 0 ≤ S → 6 * qMp ^ 2 * compositeDelta (17 / 37 * S) S (549 / 1000) = qPi0 ^ 2 →
        (-1.005 : ℝ) < (qMp * √(6 * compositeDelta S (qP * S) (549 / 1000)) - 497.611) / 0.013 ∧
          (qMp * √(6 * compositeDelta S (qP * S) (549 / 1000)) - 497.611) / 0.013 < -0.995) ∧
    ((-0.005 : ℝ) < (qMp * √(6 * compositeDelta Table.Row.Sd (19961420 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
      (qMp * √(6 * compositeDelta Table.Row.Sd (19961420 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < 0.005) ∧
    ((-1.005 : ℝ) < (qMp * √(6 * compositeDelta Table.Row.Sd (19960252 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
      (qMp * √(6 * compositeDelta Table.Row.Sd (19960252 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < -0.995) ∧
    ((0.995 : ℝ) < (qMp * √(6 * compositeDelta Table.Row.Sd (19962588 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
      (qMp * √(6 * compositeDelta Table.Row.Sd (19962588 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < 1.005) ∧
    ((0.1705 : ℝ) < (qMp * √(6 * compositeDelta Table.Row.Sd (qP * (100001 / 100000) * Table.Row.Sd) (8 / 15)) -
        qMp * √(6 * compositeDelta Table.Row.Sd (qP * Table.Row.Sd) (8 / 15))) / 0.013 ∧
      (qMp * √(6 * compositeDelta Table.Row.Sd (qP * (100001 / 100000) * Table.Row.Sd) (8 / 15)) -
        qMp * √(6 * compositeDelta Table.Row.Sd (qP * Table.Row.Sd) (8 / 15))) / 0.013 < 0.1715) ∧
    ((0.1774605 : ℝ) < f1 (yR (Table.Row.Sd * qP)) ∧ f1 (yR (Table.Row.Sd * qP)) < 0.1774615) ∧
    HasDerivAt deltaLevel (f1 (yR (Table.Row.Sd * qP))) (Table.Row.Sd * qP) ∧
    ((6.55e-8 : ℝ) < compositeDelta Table.Row.Sd (qP * Table.Row.Sd) (8 / 15) -
        (deltaLevel (Table.Row.Sd * qP) + Table.Row.Sd * ((1 - 8 / 15) / 5 + 8 / 15 * f1 (yR (Table.Row.Sd * qP))) -
          6 / 125 * Table.Row.Sd ^ 2) ∧
      compositeDelta Table.Row.Sd (qP * Table.Row.Sd) (8 / 15) -
          (deltaLevel (Table.Row.Sd * qP) + Table.Row.Sd * ((1 - 8 / 15) / 5 + 8 / 15 * f1 (yR (Table.Row.Sd * qP))) -
            6 / 125 * Table.Row.Sd ^ 2) < 6.65e-8) := by
  have hB : Bnd Table.Row.Sd (1.18558163507453026801854e-2 : ℝ) (1.18558163507453029173019e-2 : ℝ) := Table.Sd_mem
  have hB0 : 0 ≤ Table.Row.Sd := Table.Sd_nonneg
  have hJ : Bnd (qMp * √(6 * compositeDelta Table.Row.Sd (qP * Table.Row.Sd) (8 / 15))) (4.9761358445093629212535783e2 : ℝ) (4.9761358445093629680365343e2 : ℝ) := by
    rw [Comp.shift_kaon _ _ _ hB0, nuP_eq, nuM_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
    exact J08_of_root _ hB
  have hf1 : f1 (yR (Table.Row.Sd * qP)) =
      (4 - 3 * (4 * (2 / (3 + √(9 + 16 * Real.exp (-(Table.Row.Sd * qP))))))) /
        (8 - 3 * (4 * (2 / (3 + √(9 + 16 * Real.exp (-(Table.Row.Sd * qP))))))) := by
    rw [f1, yR, uLevel]
    ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨⟨S, hS, hv⟩, -⟩ := Comp.root_0
    refine ⟨S, hS, (Comp.pion_iff S 0).mpr ?_⟩
    have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_0]; norm_num) hS.1
    rw [Comp.light_0 S hS0]
    exact hv
  · intro S hS0 hS
    have hmem : S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0 := by
      refine Comp.root_0.2 S ?_
      have := (Comp.pion_iff S 0).mp hS
      rw [Comp.light_0 S hS0] at this
      exact this
    have hk := Comp.k0_0 S hmem
    exact ⟨hk.strict (by norm_num) (by norm_num), Comp.widths_of _ _ _ _ _ hk (by norm_num) (by norm_num)⟩
  · obtain ⟨⟨S, hS, hv⟩, -⟩ := Comp.root_1
    refine ⟨S, hS, (Comp.pion_iff S 1).mpr ?_⟩
    have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_1]; norm_num) hS.1
    rw [Comp.light_1 S hS0]
    exact hv
  · intro S hS0 hS
    have hmem : S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1 := by
      refine Comp.root_1.2 S ?_
      have := (Comp.pion_iff S 1).mp hS
      rw [Comp.light_1 S hS0] at this
      exact this
    have hk := Comp.k0_1 S hmem
    exact ⟨hk.strict (by norm_num) (by norm_num), Comp.widths_of _ _ _ _ _ hk (by norm_num) (by norm_num)⟩
  · obtain ⟨⟨S, hS, hv⟩, -⟩ := Comp.root_b
    refine ⟨S, hS, (Comp.pion_iff S (5359 / 10000)).mpr ?_⟩
    have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_b]; norm_num) hS.1
    rw [Comp.light_b S hS0]
    exact hv
  · intro S hS0 hS
    have hmem : S ∈ Set.Icc QK.sdLo_b QK.sdHi_b := by
      refine Comp.root_b.2 S ?_
      have := (Comp.pion_iff S (5359 / 10000)).mp hS
      rw [Comp.light_b S hS0] at this
      exact this
    exact Comp.widths_of _ _ _ _ _ (Comp.k0_b S hmem) (by norm_num) (by norm_num)
  · obtain ⟨⟨S, hS, hv⟩, -⟩ := Comp.root_a
    refine ⟨S, hS, (Comp.pion_iff S (5229 / 10000)).mpr ?_⟩
    have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_a]; norm_num) hS.1
    rw [Comp.light_a S hS0]
    exact hv
  · intro S hS0 hS
    have hmem : S ∈ Set.Icc QK.sdLo_a QK.sdHi_a := by
      refine Comp.root_a.2 S ?_
      have := (Comp.pion_iff S (5229 / 10000)).mp hS
      rw [Comp.light_a S hS0] at this
      exact this
    exact Comp.widths_of _ _ _ _ _ (Comp.k0_a S hmem) (by norm_num) (by norm_num)
  · obtain ⟨⟨S, hS, hv⟩, -⟩ := Comp.root_d
    refine ⟨S, hS, (Comp.pion_iff S (549 / 1000)).mpr ?_⟩
    have hS0 : 0 ≤ S := le_trans (by rw [QK.sdLo_d]; norm_num) hS.1
    rw [Comp.light_d S hS0]
    exact hv
  · intro S hS0 hS
    have hmem : S ∈ Set.Icc QK.sdLo_d QK.sdHi_d := by
      refine Comp.root_d.2 S ?_
      have := (Comp.pion_iff S (549 / 1000)).mp hS
      rw [Comp.light_d S hS0] at this
      exact this
    exact Comp.widths_of _ _ _ _ _ (Comp.k0_d S hmem) (by norm_num) (by norm_num)
  · have hk : Bnd (qMp * √(6 * compositeDelta Table.Row.Sd (19961420 / 1000000 * Table.Row.Sd) (8 / 15))) (4.9761099808910797094155307e2 : ℝ) (4.9761099808910797561982729e2 : ℝ) := by
      rw [Comp.shift_kaon _ _ _ hB0, Comp.pNuP_m_eq, Comp.pNuM_m_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
      exact QK.K0p_m _ hB
    exact Comp.widths_of _ _ _ _ _ hk (by norm_num) (by norm_num)
  · have hk : Bnd (qMp * √(6 * compositeDelta Table.Row.Sd (19960252 / 1000000 * Table.Row.Sd) (8 / 15))) (4.9759799889745222168434677e2 : ℝ) (4.9759799889745222636251709e2 : ℝ) := by
      rw [Comp.shift_kaon _ _ _ hB0, Comp.pNuP_lo_eq, Comp.pNuM_lo_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
      exact QK.K0p_lo _ hB
    exact Comp.widths_of _ _ _ _ _ hk (by norm_num) (by norm_num)
  · have hk : Bnd (qMp * √(6 * compositeDelta Table.Row.Sd (19962588 / 1000000 * Table.Row.Sd) (8 / 15))) (4.9762399684543915208539599e2 : ℝ) (4.9762399684543915676377469e2 : ℝ) := by
      rw [Comp.shift_kaon _ _ _ hB0, Comp.pNuP_hi_eq, Comp.pNuM_hi_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
      exact QK.K0p_hi _ hB
    exact Comp.widths_of _ _ _ _ _ hk (by norm_num) (by norm_num)
  · have hs : Bnd (qMp * √(6 * compositeDelta Table.Row.Sd (qP * (100001 / 100000) * Table.Row.Sd) (8 / 15))) (4.9761580601368200595947404e2 : ℝ) (4.976158060136820106377875e2 : ℝ) := by
      rw [Comp.shift_kaon _ _ _ hB0, Comp.sNuP_eq, Comp.sNuM_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
      exact QK.K0_sens _ hB
    have hd := Article.Bnd.sub hs hJ
    constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith [hd.1]
    · rw [div_lt_iff₀ (by norm_num)]; linarith [hd.2]
  · rw [hf1]
    exact (QK.d1prime_Ss _ hB).strict (by norm_num) (by norm_num)
  · exact Article.deriv_delta_eq _
  · rw [Comp.shift_kaon _ _ _ hB0, nuP_eq, nuM_eq, hf1, Article.deltaLevel_eq, Article.deltaLevel_eq, Article.deltaLevel_eq]
    exact (QK.shift_rem _ hB).strict (by norm_num) (by norm_num)

end Comparison.System
