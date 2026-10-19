import Comparison.Article.Couplings

/-!
# The input units and the proton

The electron's `m_e c² = 0.51099895069 MeV` (the unit of every mass), `ħc` and
`ħ` from the SI values of `h`, `c` and `e`, the megaparsec in femtometres, and the numbers of the proton:
`log(5/2)`, `m_p/m_e`, `m_n/m_p`, `m_p`, `m_n`, `W`.
-/

namespace Comparison.Article

open Real

/-- The electron's rest energy in MeV, `0.51099895069` (CODATA 2022), the unit. -/
noncomputable def qMe : ℝ :=
  ((51099895069 : ℝ) / 100000000000)

theorem qMe_bnd : Bnd qMe (5.1099895069e-1 : ℝ) (5.1099895069e-1 : ℝ) := by
  unfold qMe
  have h1 : Bnd ((51099895069 : ℝ) / 100000000000) ((51099895069 : ℝ) / 100000000000) ((51099895069 : ℝ) / 100000000000) := Bnd.const _
  exact h1.weak (by norm_num) (by norm_num)

/-- `ħc` in MeV fm from the SI `h`, `c`, `e`. -/
noncomputable def qHc : ℝ :=
  (((6621486190496429 : ℝ) / 5340588780000) / ((2 : ℝ) * π))

theorem qHc_bnd : Bnd qHc (1.9732698045930246589043233e2 : ℝ) (1.9732698045930246589106045e2 : ℝ) := by
  unfold qHc
  have h1 : Bnd ((6621486190496429 : ℝ) / 5340588780000) ((6621486190496429 : ℝ) / 5340588780000) ((6621486190496429 : ℝ) / 5340588780000) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 := Bnd.mul h2 bnd_pi (by norm_num) (by norm_num)
  have h4 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.div h1 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((6621486190496429 : ℝ) / 5340588780000) / ((2 : ℝ) * π))) (1.9732698045930246589043233e2 : ℝ) (1.9732698045930246589106045e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- `ħ` in MeV s. -/
noncomputable def qHbar : ℝ :=
  (((44173801 : ℝ) / 10681177560000000000000000000) / ((2 : ℝ) * π))

theorem qHbar_bnd : Bnd qHbar (6.5821195695090656980580989e-22 : ℝ) (6.5821195695090656980790505e-22 : ℝ) := by
  unfold qHbar
  have h1 : Bnd ((44173801 : ℝ) / 10681177560000000000000000000) ((44173801 : ℝ) / 10681177560000000000000000000) ((44173801 : ℝ) / 10681177560000000000000000000) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 := Bnd.mul h2 bnd_pi (by norm_num) (by norm_num)
  have h4 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.div h1 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((44173801 : ℝ) / 10681177560000000000000000000) / ((2 : ℝ) * π))) (6.5821195695090656980580989e-22 : ℝ) (6.5821195695090656980790505e-22 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- `log(5/2) = log k₀(-1/4)`, the Gram-determinant term's logarithm. -/
noncomputable def qLog52 : ℝ :=
  (Real.log ((5 : ℝ) / 2))

theorem qLog52_bnd : Bnd qLog52 (9.16290731874155065183527e-1 : ℝ) (9.16290731874155065183528e-1 : ℝ) := by
  unfold qLog52
  have h1 : Bnd ((5 : ℝ) / 2) ((5 : ℝ) / 2) ((5 : ℝ) / 2) := Bnd.const _
  have h2 : Bnd ((Real.log ((5 : ℝ) / 2))) (9.16290731874155065183527e-1 : ℝ) (9.16290731874155065183528e-1 : ℝ) := Bnd.log h1 (by norm_num) (le_trans (exp_le' (9.16290731874155065183527e-1 : ℝ) (((916290731874155065183527 : ℝ) / 1000000000000000000000000)) (2.4999999999999999999999995 : ℝ) 28 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (9.16290731874155065183528e-1 : ℝ) (((114536341484269383147941 : ℝ) / 125000000000000000000000)) (2.5000000000000000000000019 : ℝ) 28 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  exact h2

/-- **The proton's pole** `m_p/m_e = 6M + C_h + (1/6) log(5/2) − a⁵ − b a⁶`. -/
noncomputable def qRp : ℝ :=
  ((((1836 : ℝ) + (((1 : ℝ) / 6) * qLog52)) - ((3125 : ℝ) / 79235168)) - ((109375 : ℝ) / 48174982144))

theorem qRp_bnd : Bnd qRp (1.8361526734120517861459969e3 : ℝ) (1.8361526734120517861459972e3 : ℝ) := by
  unfold qRp
  have h1 : Bnd (1836 : ℝ) (1836 : ℝ) (1836 : ℝ) := Bnd.const _
  have h2 : Bnd ((1 : ℝ) / 6) ((1 : ℝ) / 6) ((1 : ℝ) / 6) := Bnd.const _
  have h3 := Bnd.mul h2 qLog52_bnd (by norm_num) (by norm_num)
  have h4 : Bnd ((((1 : ℝ) / 6) * qLog52)) (1.527151219790258441972545e-1 : ℝ) (1.5271512197902584419725467e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.add h1 h4
  have h6 : Bnd (((1836 : ℝ) + (((1 : ℝ) / 6) * qLog52))) (1.8361527151219790258441972e3 : ℝ) (1.8361527151219790258441973e3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((3125 : ℝ) / 79235168) ((3125 : ℝ) / 79235168) ((3125 : ℝ) / 79235168) := Bnd.const _
  have h8 := Bnd.sub h6 h7
  have h9 : Bnd ((((1836 : ℝ) + (((1 : ℝ) / 6) * qLog52)) - ((3125 : ℝ) / 79235168))) (1.8361526756824210760207046e3 : ℝ) (1.8361526756824210760207048e3 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd ((109375 : ℝ) / 48174982144) ((109375 : ℝ) / 48174982144) ((109375 : ℝ) / 48174982144) := Bnd.const _
  have h11 := Bnd.sub h9 h10
  have h12 : Bnd (((((1836 : ℝ) + (((1 : ℝ) / 6) * qLog52)) - ((3125 : ℝ) / 79235168)) - ((109375 : ℝ) / 48174982144))) (1.8361526734120517861459969e3 : ℝ) (1.8361526734120517861459972e3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  exact h12

/-- The proton's mass in MeV, `m_e · m_p/m_e`. -/
noncomputable def qMp : ℝ :=
  (qMe * qRp)

theorem qMp_bnd : Bnd qMp (9.3827208942019672472054469e2 : ℝ) (9.3827208942019672472054485e2 : ℝ) := by
  unfold qMp
  have h1 := Bnd.mul qMe_bnd qRp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMe * qRp)) (9.3827208942019672472054469e2 : ℝ) (9.3827208942019672472054485e2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **`m_n/m_p = (5/2)^{5a⁴ + 4a¹⁰ + 10c_L b a⁶}`**, as `exp(log(5/2) κ_n)`. -/
noncomputable def qRn : ℝ :=
  (Real.exp (qLog52 * ((349210004165625 : ℝ) / 232293838375564288)))

theorem qRn_bnd : Bnd qRn (1.0013784195646195665100965 : ℝ) (1.0013784195646195665100966 : ℝ) := by
  unfold qRn
  have h1 : Bnd ((349210004165625 : ℝ) / 232293838375564288) ((349210004165625 : ℝ) / 232293838375564288) ((349210004165625 : ℝ) / 232293838375564288) := Bnd.const _
  have h2 := Bnd.mul qLog52_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qLog52 * ((349210004165625 : ℝ) / 232293838375564288))) (1.3774704164876236366923294e-3 : ℝ) (1.377470416487623636692331e-3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((Real.exp (qLog52 * ((349210004165625 : ℝ) / 232293838375564288)))) (1.0013784195646195665100965 : ℝ) (1.0013784195646195665100966 : ℝ) := Bnd.exp h3 (exp_ge' (1.3774704164876236366923294e-3 : ℝ) (((6887352082438118183461647 : ℝ) / 5000000000000000000000000000)) (1.0013784195646195665100965 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (1.377470416487623636692331e-3 : ℝ) (((1377470416487623636692331 : ℝ) / 1000000000000000000000000000)) (1.0013784195646195665100966 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  exact h4

/-- The neutron's mass in MeV. -/
noncomputable def qMn : ℝ :=
  (qMp * qRn)

theorem qMn_bnd : Bnd qMn (9.3956542202519000326659123e2 : ℝ) (9.3956542202519000326659149e2 : ℝ) := by
  unfold qMn
  have h1 := Bnd.mul qMp_bnd qRn_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMp * qRn)) (9.3956542202519000326659123e2 : ℝ) (9.3956542202519000326659149e2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- Gravity's amplitude `W = (2/5)⁴⁸(295/296)⁹`. -/
noncomputable def qW : ℝ :=
  ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625)

theorem qW_bnd : Bnd qW ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625) ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625) := by
  unfold qW
  have h1 : Bnd ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625) ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625) ((18167619007083842633728 : ℝ) / 236399027553628911846317350864410400390625) := Bnd.const _
  exact h1

end Comparison.Article
